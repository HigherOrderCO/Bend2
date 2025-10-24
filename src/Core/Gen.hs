module Core.Gen
  ( GenInfo(..)
  , collectGenInfos
  , cutName
  , bookHasMet
  , generateDefinitions
  , applyGenerated
  , buildGenDepsBook
  , fillBook
  ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List (foldl', isPrefixOf, sortOn)
import Data.Maybe (mapMaybe)
import Control.Monad (when, unless)
import System.Exit (ExitCode(..))
import System.IO (hClose, hPutStr)
import System.IO.Temp (withSystemTempFile)
import System.Process (readProcessWithExitCode)
import System.Timeout (timeout)
import Debug.Trace

import Core.Deps (getDeps)
import Core.Show (cutName)
import Core.Type
import Target.HVM.HVM (HCore)
import qualified Target.HVM.HVM as HVM
import Target.HVM.Parse (parseGeneratedTerms)
import Target.HVM.Pretty (prettyGenerated)

-------------------------------------------------------------------------------
-- Metadata about generator targets
-------------------------------------------------------------------------------

data GenInfo = GenInfo
  { giFullName   :: Name
  , giSimpleName :: String
  , giSpan       :: Span
  , giMetTerm    :: Term
  , giType       :: Type
  , giCtxTerms   :: [Term]
  }

collectGenInfos :: FilePath -> Book -> [GenInfo]
collectGenInfos file (Book defs names _) = mapMaybe lookupGen names
  where
    lookupGen name = do
      (_, term, typ) <- M.lookup name defs
      case term of
        Loc sp inner | spanPth sp == file -> 
          case stripLoc inner of
            met@(Met _ metType metCtx) -> Just (GenInfo name (cutName name) sp met metType metCtx)
            _                          -> Nothing
        _ -> Nothing
    stripLoc t = case t of
      Loc _ inner -> stripLoc inner
      other       -> other

-------------------------------------------------------------------------------
-- Generation pipeline
-------------------------------------------------------------------------------

fillBook :: FilePath -> String -> String -> Book -> Book -> IO (Result String)
fillBook path mainFQN content rawBook adjustedBook = do
  let genInfos = collectGenInfos path rawBook
  eDefs <- generateDefinitions path adjustedBook mainFQN genInfos
  pure $ do
    defs    <- eitherToResult eDefs
    updated <- eitherToResult (applyGenerated content genInfos defs)
    pure updated
  where
    eitherToResult :: Either String a -> Result a
    eitherToResult = either (\msg -> Fail (Unsupported noSpan (Ctx []) (Just msg))) Done

generateDefinitions :: FilePath -> Book -> Name -> [GenInfo] -> IO (Either String (M.Map String String))
generateDefinitions _file book mainFQN genInfos = do
  let hvmCode = HVM.compile book mainFQN

  -- Run HVM compilation
  hvmResult <- withSystemTempFile "bend-gen.hvm4" $ \tmpPath tmpHandle -> do
    hPutStr tmpHandle hvmCode
    hClose tmpHandle
    timeout (5 * 1000000) (readProcessWithExitCode "hvm4" [tmpPath, "-C1"] "")

  return (generateDefinitionsGo hvmResult genInfos)

generateDefinitionsGo :: Maybe (ExitCode, String, String) -> [GenInfo] -> Either String (M.Map String String)
generateDefinitionsGo hvmResult genInfos = do
  case hvmResult of
    Nothing                                                   -> Left $ "hvm4 timed out while generating code."
    Just (ExitFailure code,    _, stderrStr)                  -> Left $ "hvm4 exited with code " ++ show code ++ ": " ++ stderrStr
    Just (ExitSuccess, stdoutStr, stderrStr) | null stdoutStr -> Left $ "hvm4 reported an error: " ++ stderrStr
    Just (ExitSuccess, stdoutStr, stderrStr)                  -> do
      terms <- parseGeneratedTerms stdoutStr

      -- If not all terms have been synthesized, interrupt 
      when (length terms /= length genInfos) $
        Left $ "hvm4 returned " ++ show (length terms) ++ " definitions, expected " ++ show (length genInfos)

      -- Render definitions into final map
      M.fromList <$> traverse renderDef (zip genInfos terms)
  where
    renderDef (info, term) = case prettyGenerated (giSimpleName info) (giType info) (giCtxTerms info) term of
        Left err  -> Left $ "Failed to prettify " ++ giSimpleName info ++ ": " ++ show err
        Right txt -> Right (giSimpleName info, txt)

applyGenerated :: String -> [GenInfo] -> M.Map String String -> Either String String
applyGenerated original genInfos generated = do
  replacements <- traverse toReplacement genInfos
  applyGeneratedGo original replacements
  where
    toReplacement info =
      case M.lookup (giSimpleName info) generated of
        Nothing     -> Left $ "Missing generated definition for " ++ giSimpleName info
        Just result -> Right (giSpan info, ensureTrailingNewline result)

    ensureTrailingNewline txt
      | null txt         = txt
      | last txt == '\n' = txt
      | otherwise        = txt ++ "\n"

applyGeneratedGo :: String -> [(Span, String)] -> Either String String
applyGeneratedGo original replacements = do
  converted <- traverse toOffsets replacements
  let sortedAsc  = sortOn (\(s,_,_) ->  s) converted
  let sortedDesc = reverse sortedAsc

  when (overlapping sortedAsc) $ 
    Left "Generator definitions overlap; cannot rewrite file."

  return $ foldl' applyOne original sortedDesc

  where
    overlapping offsets = case offsets of
      ((_, e1, _): (s2, e2, t2) : rest) -> e1 > s2 || overlapping ((s2, e2, t2) : rest)
      _                                 -> False

    toOffsets (sp, txt) = do
      let src       = spanSrc sp
          reference = if null src then original else src
          start     = positionToOffset reference (spanBeg sp)
          end       = positionToOffset reference (spanEnd sp)
      unless (start <= end && end <= length reference) $
        Left "Invalid span information for generator replacement."
      return (start, end, txt)

    positionToOffset src (line, col)
      | line <= 0 || col <= 0 = 0
      | otherwise             = lineStartOffset src (line - 1) + (col - 1)
    
    lineStartOffset :: String -> Int -> Int
    lineStartOffset src linesToSkip = go src linesToSkip 0
      where
        go remaining 0 acc = acc
        go [] _ acc = acc
        go s n acc =
          let (before, after) = break (== '\n') s
              consumed = acc + length before
          in case after of
               []       -> consumed
               (_:rest) -> go rest (n - 1) (consumed + 1)
    
    applyOne acc (start, end, txt) =
      let (prefix, rest) = splitAt start acc
          (_,    suffix) = splitAt (end - start) rest
      in prefix ++ txt ++ suffix


-------------------------------------------------------------------------------
-- Dependency closure for generator books
-------------------------------------------------------------------------------

buildGenDepsBook :: Book -> Book
buildGenDepsBook book@(Book defs names m) = Book finalDefs finalNames m
  where
    genDefs = M.filter (\(_, term, _) -> hasMet term) defs
    genNames = M.keysSet genDefs

    allDefs = M.toList defs
    reverseDeps = S.fromList
      [ name
      | (name, (_, term, typ)) <- allDefs
      , not (name `S.member` genNames)
      , let deps = S.union (getDeps term) (getDeps typ)
      , not (S.null (S.intersection genNames deps))
      ]

    targetDefs = M.filterWithKey (\k _ -> k `S.member` genNames || k `S.member` reverseDeps) defs
    allDeps = S.unions
      [ S.union (getDeps term) (getDeps typ)
      | (_, term, typ) <- M.elems targetDefs
      ]

    allNames = S.union genNames reverseDeps
    finalDepNames = S.union allNames allDeps

    finalDefs = M.filterWithKey (\k _ -> k `S.member` finalDepNames) defs
    finalNames = filter (`S.member` finalDepNames) names

-------------------------------------------------------------------------------
-- Met detection
-------------------------------------------------------------------------------
--
bookHasMet :: Book -> Bool
bookHasMet (Book defs _ _) =
  any (\(_, term, _) -> hasMet term) (M.elems defs) -- TODO: why not checkc the type?

hasMet :: Term -> Bool
hasMet term = case term of
  Met {}      -> True
  Sub t       -> hasMet t
  Fix _ f     -> hasMet (f (Var "" 0))
  Let k t v f -> case t of
    Just t'   -> hasMet t' || hasMet v || hasMet (f (Var k 0))
    Nothing   -> hasMet v || hasMet (f (Var k 0))
  Use k v f   -> hasMet v || hasMet (f (Var k 0))
  Chk x t     -> hasMet x || hasMet t
  EmpM        -> False
  UniM f      -> hasMet f
  BitM f t    -> hasMet f || hasMet t
  Suc n       -> hasMet n
  NatM z s    -> hasMet z || hasMet s
  Lst t       -> hasMet t
  Con h t     -> hasMet h || hasMet t
  LstM n c    -> hasMet n || hasMet c
  EnuM cs e   -> any (hasMet . snd) cs || hasMet e
  Op2 _ a b   -> hasMet a || hasMet b
  Op1 _ a     -> hasMet a
  Sig a b     -> hasMet a || hasMet b
  Tup a b     -> hasMet a || hasMet b
  SigM f      -> hasMet f
  All a b     -> hasMet a || hasMet b
  Lam _ t f   -> maybe False hasMet t || hasMet (f (Var "" 0))
  App f x     -> hasMet f || hasMet x
  Eql t a b   -> hasMet t || hasMet a || hasMet b
  EqlM f      -> hasMet f
  Rwt e f     -> hasMet e || hasMet f
  Sup _ a b   -> hasMet a || hasMet b
  SupM l f    -> hasMet l || hasMet f
  Loc _ t     -> hasMet t
  Log s x     -> hasMet s || hasMet x
  Pat s m c   -> any hasMet s || any (hasMet . snd) m || any (\(p,b) -> any hasMet p || hasMet b) c
  Frk l a b   -> hasMet l || hasMet a || hasMet b
  _           -> False
