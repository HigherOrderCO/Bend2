module Core.CLI.Gen
  ( GenInfo(..)
  , collectGenInfos
  , bookHasMet
  , generateDefinitions
  , applyGenerated
  , buildGenDepsBook
  ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List (foldl', sortOn)
import System.Exit (ExitCode(..))
import System.IO (hClose, hPutStr)
import System.IO.Temp (withSystemTempFile)
import System.Process (readProcessWithExitCode)
import System.Timeout (timeout)

import Core.Deps (getDeps)
import Core.Type
import Core.Gen.Info (GenInfo(..), collectGenInfos)
import Core.Gen.Parser (parseGeneratedTerms)
import Core.Gen.Pretty (prettyGenerated)
import qualified Target.HVM as HVM

bookHasMet :: Book -> Bool
bookHasMet (Book defs _) = any (\(_, term, _) -> hasMet term) (M.elems defs)

generateDefinitions :: FilePath -> Book -> Name -> [GenInfo] -> IO (Either String (M.Map String String))
generateDefinitions _file book mainFQN genInfos = do
  let hvmCode = HVM.compile book mainFQN
  withSystemTempFile "bend-gen.hvm4" $ \tmpPath tmpHandle -> do
    hPutStr tmpHandle hvmCode
    hClose tmpHandle
    result <- timeout (5 * 1000000) (readProcessWithExitCode "hvm4" [tmpPath, "-C1"] "")
    case result of
      Nothing -> pure $ Left "hvm4 timed out while generating code."
      Just (exitCode, stdoutStr, stderrStr) -> case exitCode of
        ExitSuccess ->
          if not (null stderrStr)
            then pure $ Left $ "hvm4 reported an error: " ++ stderrStr
            else case parseGeneratedTerms stdoutStr of
              Left err -> pure (Left err)
              Right terms ->
                if length terms < length genInfos
                  then pure $ Left $ "hvm4 did not return enough definitions. Expected "
                                    ++ show (length genInfos) ++ ", received " ++ show (length terms)
                  else if length terms > length genInfos
                    then pure $ Left $ "hvm4 returned extra definitions. Expected "
                                      ++ show (length genInfos) ++ ", received " ++ show (length terms)
                  else do
                    let paired = zip genInfos terms
                    case traverse renderDefinition paired of
                      Left err -> pure (Left err)
                      Right rendered ->
                        pure (Right (M.fromList rendered))
        ExitFailure code ->
          pure $ Left $ "hvm4 exited with code " ++ show code ++ ": " ++ stderrStr

  where
    renderDefinition (info, term) =
      case prettyGenerated info term of
        Left err  -> Left $ "Failed to prettify " ++ giSimpleName info ++ ": " ++ show err
        Right txt -> Right (giSimpleName info, txt)

applyGenerated :: String -> [GenInfo] -> M.Map String String -> Either String String
applyGenerated content genInfos generated = do
  replacements <- traverse toReplacement genInfos
  applySpanReplacements content replacements
  where
    toReplacement info =
      case M.lookup (giSimpleName info) generated of
        Nothing     -> Left $ "Missing generated definition for " ++ giSimpleName info
        Just result -> Right (giSpan info, ensureTrailingNewline result)

ensureTrailingNewline :: String -> String
ensureTrailingNewline txt
  | null txt = txt
  | last txt == '\n' = txt
  | otherwise = txt ++ "\n"

applySpanReplacements :: String -> [(Span, String)] -> Either String String
applySpanReplacements original replacements = do
  converted <- traverse toOffsets replacements
  let sortedAsc = sortOn (\(s,_,_) -> s) converted
  if not (nonOverlapping sortedAsc)
    then Left "Generator definitions overlap; cannot rewrite file."
    else
      let sortedDesc = sortOn (\(s,_,_) -> negate s) converted
      in pure $ foldl' applyOne original sortedDesc
  where
    toOffsets (sp, txt) = do
      let src = spanSrc sp
          reference = if null src then original else src
          start = positionToOffset reference (spanBeg sp)
          end   = positionToOffset reference (spanEnd sp)
      if start <= end && end <= length reference
        then Right (start, end, txt)
        else Left "Invalid span information for generator replacement."
    nonOverlapping [] = True
    nonOverlapping [_] = True
    nonOverlapping ((_,e1,_):(s2,e2,x2):rest) =
      e1 <= s2 && nonOverlapping ((s2,e2,x2):rest)
    applyOne acc (start, end, txt) =
      let (prefix, rest) = splitAt start acc
          (_, suffix) = splitAt (end - start) rest
      in prefix ++ txt ++ suffix

positionToOffset :: String -> (Int, Int) -> Int
positionToOffset src (line, col)
  | line <= 0 || col <= 0 = 0
  | otherwise =
      lineStartOffset src (line - 1) + (col - 1)

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

buildGenDepsBook :: Book -> Book
buildGenDepsBook book@(Book defs names) =
  Book finalDefs finalNames
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
