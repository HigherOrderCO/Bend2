module Core.Import
  ( autoImport
  , autoImportWithExplicit
  , extractModuleName
  ) where

import Control.Monad (when)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Char (isUpper)
import Data.List (intercalate, isInfixOf, isSuffixOf, foldl')
import Data.List.Split (splitOn)
import System.Directory (doesFileExist, getCurrentDirectory, canonicalizePath)
import System.Exit (exitFailure)
import System.FilePath ((</>))
import qualified System.FilePath as FP
import System.IO (hPutStrLn, stderr)

import Core.Deps
import Core.Parse.Book (doParseBook)
import Core.Parse.Parse (ParserState(..), Import(..))
import Core.Type
import qualified Package.Index as PkgIndex

-- Substitution structures ----------------------------------------------------

data SubstMap = SubstMap
  { functionMap :: M.Map Name Name
  , prefixMap   :: M.Map Name Name
  } deriving (Show, Eq)

emptySubstMap :: SubstMap
emptySubstMap = SubstMap M.empty M.empty

unionSubstMap :: SubstMap -> SubstMap -> SubstMap
unionSubstMap (SubstMap f1 p1) (SubstMap f2 p2) =
  SubstMap (M.union f1 f2) (M.union p1 p2)

insertFunction :: Name -> Name -> SubstMap -> SubstMap
insertFunction alias target (SubstMap f p) = SubstMap (M.insert alias target f) p

insertPrefix :: Name -> Name -> SubstMap -> SubstMap
insertPrefix alias target (SubstMap f p) = SubstMap f (M.insert alias target p)

applyFunctionSubst :: SubstMap -> Name -> Name
applyFunctionSubst subst name =
  case M.lookup name (functionMap subst) of
    Just replacement -> replacement
    Nothing -> applyPrefixSubst subst name

applyPrefixSubst :: SubstMap -> Name -> Name
applyPrefixSubst subst name =
  case splitOn "::" name of
    alias:rest | not (null rest) ->
      case M.lookup alias (prefixMap subst) of
        Just prefix -> prefix ++ "::" ++ intercalate "::" rest
        Nothing -> name
    _ -> name

applyNameSubst :: SubstMap -> Name -> Name
applyNameSubst subst name =
  let fnReplaced = applyFunctionSubst subst name
  in if fnReplaced /= name
        then fnReplaced
        else name

applyNameSubstSet :: SubstMap -> S.Set Name -> S.Set Name
applyNameSubstSet subst = S.map (applyNameSubst subst)

-- Substitution on terms ------------------------------------------------------

substituteRefs :: SubstMap -> Term -> Term
substituteRefs subst = go S.empty
  where
    resolveName = applyFunctionSubst subst

    go bound term = case term of
      Var k i     -> if k `S.member` bound then Var k i else Var (resolveName k) i
      Ref k i     -> Ref (resolveName k) i
      Sym n       -> Sym n
      Sub t       -> Sub (go bound t)
      Fix k f     -> Fix k (\v -> go (S.insert k bound) (f v))
      Let k t v f -> Let k (fmap (go bound) t) (go bound v) (\u -> go (S.insert k bound) (f u))
      Use k v f   -> Use k (go bound v) (\u -> go (S.insert k bound) (f u))
      Set         -> Set
      Chk x t     -> Chk (go bound x) (go bound t)
      Tst x       -> Tst (go bound x)
      Emp         -> Emp
      EmpM        -> EmpM
      Uni         -> Uni
      One         -> One
      UniM f      -> UniM (go bound f)
      Bit         -> Bit
      Bt0         -> Bt0
      Bt1         -> Bt1
      BitM f t    -> BitM (go bound f) (go bound t)
      Nat         -> Nat
      Zer         -> Zer
      Suc n       -> Suc (go bound n)
      NatM z s    -> NatM (go bound z) (go bound s)
      Lst t       -> Lst (go bound t)
      IO t        -> IO (go bound t)
      Nil         -> Nil
      Con h t     -> Con (go bound h) (go bound t)
      LstM n c    -> LstM (go bound n) (go bound c)
      Enu cs      -> Enu cs
      EnuM cs d   -> EnuM (map (fmap (go bound)) cs) (go bound d)
      Num n       -> Num n
      Val v       -> Val v
      Op2 op a b  -> Op2 op (go bound a) (go bound b)
      Op1 op a    -> Op1 op (go bound a)
      Sig a b     -> Sig (go bound a) (case b of
                                        Lam k t f -> Lam k (fmap (go bound) t) (\x -> go (S.insert k bound) (f x))
                                        other -> go bound other)
      Tup a b     -> Tup (go bound a) (go bound b)
      SigM f      -> SigM (go bound f)
      All a b     -> All (go bound a) (case b of
                                        Lam k t f -> Lam k (fmap (go bound) t) (\x -> go (S.insert k bound) (f x))
                                        other -> go bound other)
      Lam k t f   -> Lam k (fmap (go bound) t) (\v -> go (S.insert k bound) (f v))
      App f x     -> App (go bound f) (go bound x)
      Eql t a b   -> Eql (go bound t) (go bound a) (go bound b)
      Rfl         -> Rfl
      EqlM f      -> EqlM (go bound f)
      Met n t ctx -> Met n (go bound t) (map (go bound) ctx)
      Era         -> Era
      Sup l a b   -> Sup (go bound l) (go bound a) (go bound b)
      SupM l f    -> SupM (go bound l) (go bound f)
      Loc sp t    -> Loc sp (go bound t)
      Log s x     -> Log (go bound s) (go bound x)
      Pri p       -> Pri p
      Rwt e f     -> Rwt (go bound e) (go bound f)
      Pat s m c   -> Pat (map (go bound) s)
                           (map (fmap (go bound)) m)
                           (map (\(ps, b) -> (map (go bound) ps, go bound b)) c)
      Frk l a b   -> Frk (go bound l) (go bound a) (go bound b)

substituteRefsInBook :: SubstMap -> Book -> Book
substituteRefsInBook subst (Book defs names) =
  Book (M.map (substituteInDef subst) defs) names
  where
    substituteInDef s (inj, term, typ) = (inj, substituteRefs s term, substituteRefs s typ)

-- Building substitution maps -------------------------------------------------

buildAliasSubstMap :: [Import] -> SubstMap
buildAliasSubstMap = foldl' addAlias emptySubstMap
  where
    addAlias acc (ImportAlias target alias) =
      let accWithPrefix = insertPrefix alias target acc
          accWithFunction = if "::" `isInfixOf` target
                              then insertFunction alias target accWithPrefix
                              else accWithPrefix
      in accWithFunction

buildLocalSubstMap :: FilePath -> Book -> SubstMap
buildLocalSubstMap currentFile (Book defs _) =
  let filePrefix = modulePrefix ++ "::"
      localDefs = M.filterWithKey (\k _ -> filePrefix `prefixOf` k) defs
      fnMap = foldl' collect [] (M.toList localDefs)
      fnMap' = M.fromList fnMap
  in SubstMap fnMap' M.empty
  where
    modulePrefix = extractModuleName currentFile
    prefixOf pref str = take (length pref) str == pref

    collect fs (fqn, _defn) =
      let withoutPrefix = drop (length modulePrefix + 2) fqn
      in (withoutPrefix, fqn) : fs

-- Book helpers ----------------------------------------------------------------

bookNames :: Book -> S.Set Name
bookNames (Book defs _) = S.fromList (M.keys defs)

bookDefs :: Book -> M.Map Name Defn
bookDefs (Book defs _) = defs

insertDefinition :: Book -> Name -> Defn -> Book
insertDefinition (Book defs names) name defn =
  let defs' = M.insert name defn defs
      names' = if name `elem` names then names else names ++ [name]
  in Book defs' names'

definitionDeps :: Defn -> S.Set Name
definitionDeps (_, term, typ) = S.union (getDeps term) (getDeps typ)

-- Import resolution -----------------------------------------------------------

data ImporterState = ImporterState
  { isRoot        :: FilePath
  , isIndex       :: PkgIndex.IndexConfig
  , isBook        :: Book
  , isPending     :: S.Set Name
  , isLoaded      :: S.Set Name
  , isModuleCache :: M.Map String (Book, SubstMap)
  , isSubst       :: SubstMap
  }

resolveAll :: ImporterState -> IO ImporterState
resolveAll st =
  case S.minView (isPending st) of
    Nothing -> pure st
    Just (dep, rest) -> do
      st' <- resolveDependency st { isPending = rest } dep
      resolveAll st'

resolveDependency :: ImporterState -> Name -> IO ImporterState
resolveDependency st dep
  | dep `S.member` isLoaded st = pure st
  | otherwise = do
      let resolved = applyNameSubst (isSubst st) dep
      if resolved /= dep
        then pure st { isPending = S.insert resolved (isPending st) }
        else if "::" `isInfixOf` dep
          then ensureDefinition dep st
          else if not (isModuleCandidate dep)
            then pure st { isLoaded = S.insert dep (isLoaded st) }
            else do
              st' <- ensureModuleFor dep st
              let resolved' = applyNameSubst (isSubst st') dep
              if resolved' == dep
                then do
                  hPutStrLn stderr $ "Import error: could not resolve reference '" ++ dep ++ "'."
                  exitFailure
                else pure st' { isPending = S.insert resolved' (isPending st') }

isModuleCandidate :: Name -> Bool
isModuleCandidate [] = False
isModuleCandidate (c:_) = isUpper c

ensureDefinition :: Name -> ImporterState -> IO ImporterState
ensureDefinition name st
  | name `S.member` isLoaded st = pure st
  | otherwise =
      case M.lookup name (bookDefs (isBook st)) of
        Just _ -> pure st { isLoaded = S.insert name (isLoaded st) }
        Nothing ->
          case splitFQN name of
            Nothing -> do
              hPutStrLn stderr $ "Import error: invalid fully qualified name '" ++ name ++ "'."
              exitFailure
            Just (modulePath, _) -> do
              ((moduleBook, moduleLocalSubst), st1) <- loadModule modulePath st
              let subst' = unionSubstMap (isSubst st1) moduleLocalSubst
                  st2 = st1 { isSubst = subst' }
              case M.lookup name (bookDefs moduleBook) of
                Nothing -> do
                  hPutStrLn stderr $ "Error: definition '" ++ name ++ "' not found in module '" ++ modulePath ++ "'."
                  exitFailure
                Just defn -> do
                  let book' = insertDefinition (isBook st2) name defn
                      depsForDef = S.delete name (definitionDeps defn)
                      resolvedDeps = applyNameSubstSet subst' depsForDef
                      alreadyKnown = S.union (bookNames book') (isLoaded st2)
                      newPending = S.union (isPending st2) (S.difference resolvedDeps alreadyKnown)
                  pure st2
                    { isBook = book'
                    , isLoaded = S.insert name (isLoaded st2)
                    , isPending = newPending
                    }

ensureModuleFor :: Name -> ImporterState -> IO ImporterState
ensureModuleFor modulePath st = do
  ((_, moduleLocalSubst), st1) <- loadModule modulePath st
  let subst' = unionSubstMap (isSubst st1) moduleLocalSubst
  pure st1 { isSubst = subst' }

loadModule :: String -> ImporterState -> IO ((Book, SubstMap), ImporterState)
loadModule modulePath st =
  case M.lookup modulePath (isModuleCache st) of
    Just cached -> pure (cached, st)
    Nothing -> do
      (posixPath, systemPath) <- resolveModuleFile (isRoot st) (isIndex st) modulePath
      content <- readFile (isRoot st </> systemPath)
      case doParseBook posixPath content of
        Left err -> do
          hPutStrLn stderr err
          exitFailure
        Right (book, parserState) -> do
          let aliasSubst = buildAliasSubstMap (parsedImports parserState)
              localSubst = buildLocalSubstMap posixPath book
              combined = unionSubstMap aliasSubst localSubst
              substituted = substituteRefsInBook combined book
              cacheEntry = (substituted, localSubst)
              cache' = M.insert modulePath cacheEntry (isModuleCache st)
          pure (cacheEntry, st { isModuleCache = cache' })

resolveModuleFile :: FilePath -> PkgIndex.IndexConfig -> String -> IO (String, FilePath)
resolveModuleFile root indexCfg modulePath = do
  let candidates = [modulePath ++ ".bend", modulePath ++ "/_.bend"]
  existing <- firstExisting candidates
  case existing of
    Just (posixPath, systemPath) -> pure (posixPath, systemPath)
    Nothing -> do
      _ <- mapM (attemptFetch indexCfg) candidates
      existing' <- firstExisting candidates
      case existing' of
        Just (posixPath, systemPath) -> pure (posixPath, systemPath)
        Nothing -> do
          hPutStrLn stderr $ "Error: unable to locate module '" ++ modulePath ++ "'."
          exitFailure
  where
    firstExisting [] = pure Nothing
    firstExisting (p:ps) = do
      let systemPath = fromPosixPath p
      exists <- doesFileExist (root </> systemPath)
      if exists then pure (Just (p, systemPath)) else firstExisting ps

    attemptFetch cfg p = do
      res <- PkgIndex.ensureFile cfg p
      case res of
        Left errMessage -> hPutStrLn stderr ("Warning: failed to fetch '" ++ p ++ "': " ++ errMessage) >> pure ()
        Right () -> pure ()

-- Entry points ---------------------------------------------------------------

autoImport :: FilePath -> Book -> IO Book
autoImport currentFile book = do
  root <- ensureBendRoot
  indexCfg <- PkgIndex.defaultIndexConfig root
  relFile <- normalizeRelativePath root currentFile
  let localSubst = buildLocalSubstMap relFile book
  runAutoImport root indexCfg book localSubst emptySubstMap

autoImportWithExplicit :: FilePath -> Book -> ParserState -> IO Book
autoImportWithExplicit currentFile book parserState = do
  root <- ensureBendRoot
  indexCfg <- PkgIndex.defaultIndexConfig root
  relFile <- normalizeRelativePath root currentFile
  let aliasSubst = buildAliasSubstMap (parsedImports parserState)
      localSubst = buildLocalSubstMap relFile book
  runAutoImport root indexCfg book localSubst aliasSubst

runAutoImport :: FilePath -> PkgIndex.IndexConfig -> Book -> SubstMap -> SubstMap -> IO Book
runAutoImport root indexCfg base localSubst aliasSubst = do
  let combinedSubst = unionSubstMap aliasSubst localSubst
      substitutedBase = substituteRefsInBook combinedSubst base
      initialLoaded = bookNames substitutedBase
      initialPending = S.difference (getBookDeps substitutedBase) initialLoaded
      initialState = ImporterState
        { isRoot = root
        , isIndex = indexCfg
        , isBook = substitutedBase
        , isPending = initialPending
        , isLoaded = initialLoaded
        , isModuleCache = M.empty
        , isSubst = combinedSubst
        }
  finalState <- resolveAll initialState
  let finalBook = substituteRefsInBook (isSubst finalState) (isBook finalState)
  pure finalBook

-- Utilities ------------------------------------------------------------------

ensureBendRoot :: IO FilePath
ensureBendRoot = do
  cwd <- getCurrentDirectory
  let base = FP.takeFileName (FP.normalise cwd)
  if base == "BendRoot"
    then pure cwd
    else do
      hPutStrLn stderr "Error: bend must be executed from the BendRoot directory."
      exitFailure

normalizeRelativePath :: FilePath -> FilePath -> IO FilePath
normalizeRelativePath root path = do
  absRoot <- canonicalizePath root
  absPath <- canonicalizePath path
  let rel = FP.makeRelative absRoot absPath
  when (takesParent rel) $ do
    hPutStrLn stderr $ "Error: file '" ++ path ++ "' is outside BendRoot."
    exitFailure
  pure (toPosixPath rel)
  where
    takesParent p = ".." `elem` FP.splitDirectories p

splitFQN :: Name -> Maybe (String, String)
splitFQN name =
  case splitOn "::" name of
    []      -> Nothing
    [_]     -> Nothing
    (m:xs)  -> Just (m, intercalate "::" xs)

toPosixPath :: FilePath -> FilePath
toPosixPath path =
  let normalized = FP.normalise path
      replaced = map (\c -> if c == FP.pathSeparator then '/' else c) normalized
  in dropWhile (== '/') (dropDotSlash replaced)
  where
    dropDotSlash ('.':'/':rest) = dropDotSlash rest
    dropDotSlash other          = other

fromPosixPath :: FilePath -> FilePath
fromPosixPath p = FP.joinPath (splitOn "/" p)

extractModuleName :: FilePath -> String
extractModuleName path =
  let normalized = toPosixPath path
      withoutBend = if ".bend" `isSuffixOf` normalized
                      then take (length normalized - 5) normalized
                      else normalized
      withoutUnderscore = if "/_" `isSuffixOf` withoutBend
                            then take (length withoutBend - 2) withoutBend
                            else withoutBend
  in withoutUnderscore
