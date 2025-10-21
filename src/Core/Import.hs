module Core.Import
  ( autoImport
  , autoImportWithExplicit
  , extractModuleName
  , ensureBendRoot
  ) where

import Control.Monad (when, unless)
import Control.Exception (throwIO)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List (intercalate, isSuffixOf, foldl')
import Data.List.Split (splitOn)
import System.Directory (doesFileExist, getCurrentDirectory, canonicalizePath)
import System.FilePath ((</>))
import qualified System.FilePath as FP
import Data.Char (isUpper)

import Core.Deps
import Core.Parse.Book (doParseBook)
import Core.Parse.Parse (ParserState(..), Import(..))
import Core.Type
import Core.Show (BendException(..))
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
    Nothing ->
      let expanded = applyPrefixSubst subst name
      in if expanded == name
           then name
           else applyFunctionSubst subst expanded

applyPrefixSubst :: SubstMap -> Name -> Name
applyPrefixSubst subst name =
  case span (/= '/') name of
    (alias, '/' : rest) | not (null alias) ->
      case M.lookup alias (prefixMap subst) of
        Just target -> combineAliasPath target rest
        Nothing -> legacy
    _ -> legacy
  where
    legacy =
      case splitOn "::" name of
        aliasSegment:restSegments | not (null restSegments) ->
          case M.lookup aliasSegment (prefixMap subst) of
            Just prefix -> prefix ++ "::" ++ intercalate "::" restSegments
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

splitPathSegments :: String -> [String]
splitPathSegments = filter (not . null) . splitOn "/"

lastPathSegment :: String -> Maybe String
lastPathSegment path =
  case reverse (splitPathSegments path) of
    (seg:_) -> Just seg
    []      -> Nothing

combineAliasPath :: String -> String -> String
combineAliasPath target rest =
  let targetSegs = splitPathSegments target
      restSegs   = splitPathSegments rest
      restSegs'  = case (reverse targetSegs, restSegs) of
                     (lastSeg:_, headSeg:tailSegs) | lastSeg == headSeg -> tailSegs
                     _ -> restSegs
      combined   = targetSegs ++ restSegs'
  in intercalate "/" combined

type DepOrigin = Maybe Span

insertPending :: Name -> DepOrigin -> M.Map Name DepOrigin -> M.Map Name DepOrigin
insertPending name origin = M.insertWith keepExisting name origin
  where
    keepExisting existing _ = existing

throwImportError :: DepOrigin -> String -> IO a
throwImportError origin msg =
  case origin of
    Just sp -> throwIO $ BendException (ImportError sp msg)
    Nothing -> throwIO $ BendException (CompilationError msg)

throwCompilationError :: String -> IO a
throwCompilationError msg = throwIO $ BendException (CompilationError msg)

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
    addAlias acc (ImportAlias target alias _) =
      let accWithPrefix = insertPrefix alias target acc
      in case lastPathSegment target of
           Nothing -> accWithPrefix
           Just public ->
             let fqn = target ++ "::" ++ public
                 acc1 = insertFunction alias fqn accWithPrefix
                 acc2 = insertFunction (alias ++ "/" ++ public) fqn acc1
             in acc2

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

buildExportSubstMap :: FilePath -> Book -> Either String SubstMap
buildExportSubstMap modulePath (Book defs _) =
  let modulePrefix = extractModuleName modulePath
  in case lastPathSegment modulePrefix of
    Nothing -> Left $ "Error: invalid module path '" ++ modulePath ++ "'."
    Just public ->
      let fqn = modulePrefix ++ "::" ++ public
      in case M.lookup fqn defs of
           Nothing -> Left $ "Error: public definition '" ++ fqn ++ "' not found in module '" ++ modulePrefix ++ "'."
           Just _  ->
             let entries =
                   [ (modulePrefix, fqn)
                   , (modulePrefix ++ "/" ++ public, fqn)
                   ]
                 subst = foldl' (\m (k,v) -> insertFunction k v m) emptySubstMap entries
             in Right subst

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

definitionDepOrigins :: Defn -> M.Map Name Span
definitionDepOrigins (_, term, typ) =
  let termDeps = collectDepSpans S.empty Nothing term
      typeDeps = collectDepSpans S.empty Nothing typ
  in M.union termDeps typeDeps

-- Import resolution -----------------------------------------------------------

data ImporterState = ImporterState
  { isRoot        :: FilePath
  , isIndex       :: PkgIndex.IndexConfig
  , isBook        :: Book
  , isPending     :: M.Map Name DepOrigin
  , isLoaded      :: S.Set Name
  , isModuleCache :: M.Map String (Book, SubstMap)
  , isSubst       :: SubstMap
  }

resolveAll :: ImporterState -> IO ImporterState
resolveAll st =
  case M.minViewWithKey (isPending st) of
    Nothing -> pure st
    Just ((dep, origin), rest) -> do
      let stWithout = st { isPending = rest }
      st' <- resolveDependency stWithout dep origin
      resolveAll st'

resolveDependency :: ImporterState -> Name -> DepOrigin -> IO ImporterState
resolveDependency st dep origin
  | dep `S.member` isLoaded st = pure st
  | otherwise = do
      let resolved = applyNameSubst (isSubst st) dep
      if resolved /= dep
        then pure st { isPending = insertPending resolved origin (isPending st) }
        else case splitFQN dep of
          Just _  -> ensureDefinition origin dep st
          Nothing ->
            if not (isModuleCandidate dep)
            then pure st { isLoaded = S.insert dep (isLoaded st) }
            else do
              st' <- ensureModuleFor origin dep st
              let resolved' = applyNameSubst (isSubst st') dep
              if resolved' == dep
                then throwImportError origin $ "could not resolve reference '" ++ dep ++ "'."
                else pure st' { isPending = insertPending resolved' origin (isPending st') }

isModuleCandidate :: Name -> Bool
isModuleCandidate [] = False
isModuleCandidate name = '/' `elem` name || isUpper (head name)

ensureDefinition :: DepOrigin -> Name -> ImporterState -> IO ImporterState
ensureDefinition origin name st
  | name `S.member` isLoaded st = pure st
  | otherwise =
      case M.lookup name (bookDefs (isBook st)) of
        Just _ -> pure st { isLoaded = S.insert name (isLoaded st) }
        Nothing ->
          case splitFQN name of
            Nothing -> throwImportError origin $ "invalid fully qualified name '" ++ name ++ "'."
            Just (modulePath, defName) -> do
              let publicName = lastPathSegment modulePath
                  moduleAlreadyCached = M.member modulePath (isModuleCache st)
              case publicName of
                Nothing -> throwImportError origin $ "invalid module path '" ++ modulePath ++ "'."
                Just pub | defName /= pub && not moduleAlreadyCached ->
                  throwImportError origin $ "'" ++ name ++ "' is private to '" ++ modulePath ++ "'."
                _ -> pure ()
              ((moduleBook, moduleExportSubst), st1) <- loadModule origin modulePath st
              let subst' = unionSubstMap (isSubst st1) moduleExportSubst
                  st2 = st1 { isSubst = subst' }
              case M.lookup name (bookDefs moduleBook) of
                Nothing -> throwImportError origin $ "definition '" ++ name ++ "' not found in module '" ++ modulePath ++ "'."
                Just defn -> do
                  let book' = insertDefinition (isBook st2) name defn
                      depOrigins = M.delete name (definitionDepOrigins defn)
                      resolvedDeps =
                        [ (resolved, Just sp)
                        | (depName, sp) <- M.toList depOrigins
                        , let resolved = applyNameSubst subst' depName
                        , resolved /= name
                        ]
                      alreadyKnown = S.union (bookNames book') (isLoaded st2)
                      filteredDeps = filter (\(depName, _) -> depName `S.notMember` alreadyKnown) resolvedDeps
                      pending' = foldr (uncurry insertPending) (isPending st2) filteredDeps
                  pure st2
                    { isBook = book'
                    , isLoaded = S.insert name (isLoaded st2)
                    , isPending = pending'
                    }

ensureModuleFor :: DepOrigin -> Name -> ImporterState -> IO ImporterState
ensureModuleFor origin modulePath st = do
  ((_, moduleExportSubst), st1) <- loadModule origin modulePath st
  let subst' = unionSubstMap (isSubst st1) moduleExportSubst
  pure st1 { isSubst = subst' }

loadModule :: DepOrigin -> String -> ImporterState -> IO ((Book, SubstMap), ImporterState)
loadModule origin modulePath st =
  case M.lookup modulePath (isModuleCache st) of
    Just cached -> pure (cached, st)
    Nothing -> do
      (posixPath, systemPath) <- resolveModuleFile origin (isRoot st) (isIndex st) modulePath
      content <- readFile (isRoot st </> systemPath)
      case doParseBook posixPath content of
        Left err -> throwCompilationError err
        Right (book, parserState) -> do
          let aliasSubst = buildAliasSubstMap (parsedImports parserState)
              localSubst = buildLocalSubstMap posixPath book
              combined = unionSubstMap aliasSubst localSubst
              substituted = substituteRefsInBook combined book
          exportSubst <- case buildExportSubstMap posixPath substituted of
                           Left errMsg -> throwCompilationError errMsg
                           Right subst -> pure subst
          let cacheEntry = (substituted, exportSubst)
              cache' = M.insert modulePath cacheEntry (isModuleCache st)
          pure (cacheEntry, st { isModuleCache = cache' })

resolveModuleFile :: DepOrigin -> FilePath -> PkgIndex.IndexConfig -> String -> IO (String, FilePath)
resolveModuleFile origin root indexCfg modulePath = do
  let candidates = [modulePath ++ ".bend", modulePath ++ "/_.bend"]
  existing <- firstExisting candidates
  case existing of
    Just (posixPath, systemPath) -> pure (posixPath, systemPath)
    Nothing -> do
      fetchSequential indexCfg candidates
      existing' <- firstExisting candidates
      case existing' of
        Just (posixPath, systemPath) -> pure (posixPath, systemPath)
        Nothing -> throwImportError origin $ "unable to locate module '" ++ modulePath ++ "'."
  where
    firstExisting [] = pure Nothing
    firstExisting (p:ps) = do
      let systemPath = fromPosixPath p
      exists <- doesFileExist (root </> systemPath)
      if exists then pure (Just (p, systemPath)) else firstExisting ps

    fetchSequential _ [] = pure ()
    fetchSequential cfg (p:ps) = do
      success <- attemptFetch cfg p
      unless success (fetchSequential cfg ps)

    attemptFetch cfg p = do
      res <- PkgIndex.ensureFile cfg p
      case res of
        Left _  -> pure False
        Right () -> pure True

-- Entry points ---------------------------------------------------------------

autoImport :: FilePath -> Book -> IO Book
autoImport currentFile book = do
  root <- ensureBendRoot
  indexCfg <- PkgIndex.defaultIndexConfig root
  relFile <- normalizeRelativePath root currentFile
  let localSubst = buildLocalSubstMap relFile book
  runAutoImport root indexCfg book localSubst emptySubstMap []

autoImportWithExplicit :: FilePath -> Book -> ParserState -> IO Book
autoImportWithExplicit currentFile book parserState = do
  root <- ensureBendRoot
  indexCfg <- PkgIndex.defaultIndexConfig root
  relFile <- normalizeRelativePath root currentFile
  let aliasSubst = buildAliasSubstMap (parsedImports parserState)
      localSubst = buildLocalSubstMap relFile book
  runAutoImport root indexCfg book localSubst aliasSubst (parsedImports parserState)

runAutoImport :: FilePath -> PkgIndex.IndexConfig -> Book -> SubstMap -> SubstMap -> [Import] -> IO Book
runAutoImport root indexCfg base localSubst aliasSubst imports = do
  let combinedSubst = unionSubstMap aliasSubst localSubst
      substitutedBase = substituteRefsInBook combinedSubst base
      initialLoaded = bookNames substitutedBase
      depOrigins = getBookDepOrigins substitutedBase
      addDepOrigin (dep, sp) acc =
        if dep `S.member` initialLoaded
          then acc
          else insertPending dep (Just sp) acc
      basePending = foldr addDepOrigin M.empty (M.toList depOrigins)
      addImportOrigin (ImportAlias target _ sp) acc =
        insertPending target (Just sp) acc
      pendingWithImports = foldr addImportOrigin basePending imports
      initialState = ImporterState
        { isRoot = root
        , isIndex = indexCfg
        , isBook = substitutedBase
        , isPending = pendingWithImports
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
    else throwCompilationError "bend must be executed from the BendRoot directory."

normalizeRelativePath :: FilePath -> FilePath -> IO FilePath
normalizeRelativePath root path = do
  absRoot <- canonicalizePath root
  absPath <- canonicalizePath path
  let rel = FP.makeRelative absRoot absPath
  when (takesParent rel) $ do
    throwCompilationError $ "file '" ++ path ++ "' is outside BendRoot."
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
