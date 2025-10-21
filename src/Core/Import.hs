-- Import Resolver
-- ===============
--
-- This module resolves every dependency required by a Bend book. It expands
-- explicit `import … as …` aliases, pulls transitive dependencies, and ensures
-- the BendRoot invariants are respected before the checker runs.

module Core.Import
  ( autoImport
  , autoImportWithExplicit
  , extractModuleName
  , ensureBendRoot
  , extractMainFQN
  ) where

import Control.Exception (throwIO)
import Control.Monad (unless, when)
import Data.Char (isUpper)
import Data.List (foldl', intercalate, isSuffixOf)
import Data.List.Split (splitOn)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Semigroup (Semigroup(..))
import System.Directory (canonicalizePath, doesFileExist, getCurrentDirectory)
import System.FilePath ((</>))
import qualified System.FilePath as FP

import Core.Deps
import Core.Parse.Book (doParseBook)
import Core.Parse.Parse (Import(..), ParserState(..))
import Core.Show (BendException(..))
import Core.Type
import qualified Package.Index as PkgIndex

data SubstMap = SubstMap
  { functionMap :: !(M.Map Name Name)
  , prefixMap   :: !(M.Map Name Name)
  } deriving (Show, Eq)

instance Semigroup SubstMap where
  SubstMap f1 p1 <> SubstMap f2 p2 = SubstMap (M.union f1 f2) (M.union p1 p2)

instance Monoid SubstMap where
  mempty = SubstMap M.empty M.empty

type DepOrigin = Maybe Span
type PendingDeps = M.Map Name DepOrigin

data ImporterState = ImporterState
  { isRoot        :: !FilePath
  , isIndex       :: !PkgIndex.IndexConfig
  , isBook        :: !Book
  , isPending     :: !PendingDeps
  , isLoaded      :: !(S.Set Name)
  , isModuleCache :: !(M.Map String (Book, SubstMap))
  , isSubst       :: !SubstMap
  }

-- Entry points ----------------------------------------------------------------

-- | Resolve every implicit dependency starting from a parsed book. This variant
-- is used when no explicit imports were recorded (for example when testing or
-- running generated code).
autoImport :: FilePath -> Book -> IO Book
autoImport currentFile book = do
  root <- ensureBendRoot
  indexCfg <- PkgIndex.defaultIndexConfig root
  relFile <- normalizeRelativePath root currentFile
  let localSubst = buildLocalSubstMap relFile book
  runAutoImport root indexCfg book localSubst mempty []

-- | Resolve dependencies honouring explicit alias imports collected by the
-- parser.
autoImportWithExplicit :: FilePath -> Book -> ParserState -> IO Book
autoImportWithExplicit currentFile book parserState = do
  root <- ensureBendRoot
  indexCfg <- PkgIndex.defaultIndexConfig root
  relFile <- normalizeRelativePath root currentFile
  let aliasSubst = buildAliasSubstMap (parsedImports parserState)
      localSubst = buildLocalSubstMap relFile book
  runAutoImport root indexCfg book localSubst aliasSubst (parsedImports parserState)

-- | Core resolver loop shared by both entry points.
runAutoImport :: FilePath -> PkgIndex.IndexConfig -> Book -> SubstMap -> SubstMap -> [Import] -> IO Book
runAutoImport root indexCfg base localSubst aliasSubst imports = do
  let combinedSubst = aliasSubst <> localSubst
      substitutedBase = substituteRefsInBook combinedSubst base
      initialLoaded = bookNames substitutedBase
      depOrigins = getBookDepOrigins substitutedBase
      pendingDeps = foldl' (accumulateDep initialLoaded) M.empty (M.toList depOrigins)
      pendingWithImports = foldl' accumulateImport pendingDeps imports
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
  pure (substituteRefsInBook (isSubst finalState) (isBook finalState))

accumulateDep :: S.Set Name -> PendingDeps -> (Name, Span) -> PendingDeps
accumulateDep loaded acc (dep, sp) =
  if dep `S.member` loaded
    then acc
    else insertPending dep (Just sp) acc

accumulateImport :: PendingDeps -> Import -> PendingDeps
accumulateImport acc (ImportAlias target _ sp) =
  insertPending target (Just sp) acc
accumulateImport acc _ = acc

-- | Ensure that the current working directory is BendRoot.
ensureBendRoot :: IO FilePath
ensureBendRoot = do
  cwd <- getCurrentDirectory
  let base = FP.takeFileName (FP.normalise cwd)
  if base == "BendRoot"
    then pure cwd
    else throwCompilationError "bend must be executed from the BendRoot directory."

-- | Extract the canonical module name for a given file path.
extractModuleName :: FilePath -> String
extractModuleName path =
  let normalized = toPosixPath path
      withoutBend =
        if ".bend" `isSuffixOf` normalized
          then take (length normalized - 5) normalized
          else normalized
      withoutUnderscore =
        if "/_" `isSuffixOf` withoutBend
          then take (length withoutBend - 2) withoutBend
          else withoutBend
  in withoutUnderscore

-- | Fully qualified name for a module's `main` definition.
extractMainFQN :: FilePath -> Book -> String
extractMainFQN path _ =
  let moduleName = extractModuleName path
  in moduleName ++ "::main"

-- Substitution utilities ------------------------------------------------------

-- | Apply the current substitution to every definition inside a book.
substituteRefsInBook :: SubstMap -> Book -> Book
substituteRefsInBook subst (Book defs names meta) =
  Book (M.map (substituteInDef subst) defs) names meta

-- | Apply substitution to a single definition tuple.
substituteInDef :: SubstMap -> Defn -> Defn
substituteInDef subst (inj, term, typ) =
  (inj, substituteRefs subst term, substituteRefs subst typ)

-- | Apply substitution to a term while respecting bound variables.
substituteRefs :: SubstMap -> Term -> Term
substituteRefs subst = substituteRefsBound subst S.empty

substituteRefsBound :: SubstMap -> S.Set Name -> Term -> Term
substituteRefsBound subst bound term =
  case term of
    Var k i -> if k `S.member` bound then Var k i else Var (applyFunctionSubst subst k) i
    Ref k i -> Ref (applyFunctionSubst subst k) i
    Sym n -> Sym n
    Sub t -> Sub (substituteRefsBound subst bound t)
    Fix k f -> Fix k (\v -> substituteRefsBound subst (S.insert k bound) (f v))
    Let k t v f ->
      Let k (fmap (substituteRefsBound subst bound) t)
          (substituteRefsBound subst bound v)
          (\u -> substituteRefsBound subst (S.insert k bound) (f u))
    Use k v f ->
      Use k (substituteRefsBound subst bound v)
          (\u -> substituteRefsBound subst (S.insert k bound) (f u))
    Set -> Set
    Chk x t -> Chk (substituteRefsBound subst bound x) (substituteRefsBound subst bound t)
    Tst x -> Tst (substituteRefsBound subst bound x)
    Emp -> Emp
    EmpM -> EmpM
    Uni -> Uni
    One -> One
    UniM f -> UniM (substituteRefsBound subst bound f)
    Bit -> Bit
    Bt0 -> Bt0
    Bt1 -> Bt1
    BitM f t -> BitM (substituteRefsBound subst bound f) (substituteRefsBound subst bound t)
    Nat -> Nat
    Zer -> Zer
    Suc n -> Suc (substituteRefsBound subst bound n)
    NatM z s -> NatM (substituteRefsBound subst bound z) (substituteRefsBound subst bound s)
    Lst t -> Lst (substituteRefsBound subst bound t)
    IO t -> IO (substituteRefsBound subst bound t)
    Nil -> Nil
    Con h t -> Con (substituteRefsBound subst bound h) (substituteRefsBound subst bound t)
    LstM n c -> LstM (substituteRefsBound subst bound n) (substituteRefsBound subst bound c)
    Enu cs -> Enu cs
    EnuM cs d ->
      EnuM (map (fmap (substituteRefsBound subst bound)) cs) (substituteRefsBound subst bound d)
    Num n -> Num n
    Val v -> Val v
    Op2 op a b -> Op2 op (substituteRefsBound subst bound a) (substituteRefsBound subst bound b)
    Op1 op a -> Op1 op (substituteRefsBound subst bound a)
    Sig a b ->
      Sig (substituteRefsBound subst bound a) (substituteBindBody subst bound b)
    Tup a b -> Tup (substituteRefsBound subst bound a) (substituteRefsBound subst bound b)
    SigM f -> SigM (substituteRefsBound subst bound f)
    All a b ->
      All (substituteRefsBound subst bound a) (substituteBindBody subst bound b)
    Lam k t f ->
      Lam k (fmap (substituteRefsBound subst bound) t)
          (\v -> substituteRefsBound subst (S.insert k bound) (f v))
    App f x -> App (substituteRefsBound subst bound f) (substituteRefsBound subst bound x)
    Eql t a b -> Eql (substituteRefsBound subst bound t)
                      (substituteRefsBound subst bound a)
                      (substituteRefsBound subst bound b)
    Rfl -> Rfl
    EqlM f -> EqlM (substituteRefsBound subst bound f)
    Met n t ctx -> Met n (substituteRefsBound subst bound t) (map (substituteRefsBound subst bound) ctx)
    Era -> Era
    Sup l a b -> Sup (substituteRefsBound subst bound l)
                      (substituteRefsBound subst bound a)
                      (substituteRefsBound subst bound b)
    SupM l f -> SupM (substituteRefsBound subst bound l) (substituteRefsBound subst bound f)
    Loc sp t -> Loc sp (substituteRefsBound subst bound t)
    Log s x -> Log (substituteRefsBound subst bound s) (substituteRefsBound subst bound x)
    Pri p -> Pri p
    Rwt e f -> Rwt (substituteRefsBound subst bound e) (substituteRefsBound subst bound f)
    Pat s m c ->
      Pat (map (substituteRefsBound subst bound) s)
          (map (fmap (substituteRefsBound subst bound)) m)
          (map (\(ps, b) -> (map (substituteRefsBound subst bound) ps, substituteRefsBound subst bound b)) c)
    Frk l a b -> Frk (substituteRefsBound subst bound l)
                      (substituteRefsBound subst bound a)
                      (substituteRefsBound subst bound b)

substituteBindBody :: SubstMap -> S.Set Name -> Term -> Term
substituteBindBody subst bound body =
  case body of
    Lam k t f ->
      let nextBound = S.insert k bound
      in Lam k (fmap (substituteRefsBound subst bound) t)
               (\x -> substituteRefsBound subst nextBound (f x))
    other -> substituteRefsBound subst bound other

-- | Substitute both direct aliases and prefix aliases in a reference.
applyNameSubst :: SubstMap -> Name -> Name
applyNameSubst subst name =
  let fnReplaced = applyFunctionSubst subst name
  in if fnReplaced /= name then fnReplaced else name

applyFunctionSubst :: SubstMap -> Name -> Name
applyFunctionSubst subst name =
  case M.lookup name (functionMap subst) of
    Just replacement -> replacement
    Nothing ->
      let expanded = applyPrefixSubst subst name
      in if expanded == name then name else applyFunctionSubst subst expanded

applyPrefixSubst :: SubstMap -> Name -> Name
applyPrefixSubst subst name =
  case span (/= '/') name of
    (alias, '/' : rest) | not (null alias) ->
      case M.lookup alias (prefixMap subst) of
        Just target -> combineAliasPath target rest
        Nothing -> name
    _ -> name

combineAliasPath :: String -> String -> String
combineAliasPath target rest =
  let targetSegs = splitPathSegments target
      restSegs = splitPathSegments rest
      adjusted =
        case (reverse targetSegs, restSegs) of
          (lastSeg : _, headSeg : tailSegs) | lastSeg == headSeg -> tailSegs
          _ -> restSegs
  in intercalate "/" (targetSegs ++ adjusted)

splitPathSegments :: String -> [String]
splitPathSegments = filter (not . null) . splitOn "/"

lastPathSegment :: String -> Maybe String
lastPathSegment path =
  case reverse (splitPathSegments path) of
    seg : _ -> Just seg
    []      -> Nothing

-- Substitution map builders ---------------------------------------------------

-- | Collect substitution entries introduced by explicit alias imports.
buildAliasSubstMap :: [Import] -> SubstMap
buildAliasSubstMap = foldl' addAlias mempty

addAlias :: SubstMap -> Import -> SubstMap
addAlias acc (ImportAlias target alias _) =
  let withPrefix = insertPrefix alias target acc
  in case lastPathSegment target of
       Nothing -> withPrefix
       Just public ->
         let fqn = target ++ "::" ++ public
             withPrimary = insertFunction alias fqn withPrefix
         in insertFunction (alias ++ "/" ++ public) fqn withPrimary

-- | Collect substitution entries that allow referring to local definitions by
-- their short names.
buildLocalSubstMap :: FilePath -> Book -> SubstMap
buildLocalSubstMap currentFile book =
  let modulePrefix = extractModuleName currentFile
      filePrefix = modulePrefix ++ "::"
      defs = bookDefs book
      localDefs = M.filterWithKey (keyHasPrefix filePrefix) defs
      mapping = foldl' (collectLocal modulePrefix) [] (M.toList localDefs)
  in SubstMap (M.fromList mapping) M.empty

keyHasPrefix :: String -> Name -> Defn -> Bool
keyHasPrefix pref key _ = take (length pref) key == pref

collectLocal :: String -> [(Name, Name)] -> (Name, Defn) -> [(Name, Name)]
collectLocal modulePrefix acc (fqn, _) =
  let withoutPrefix = drop (length modulePrefix + 2) fqn
  in (withoutPrefix, fqn) : acc

-- | Map a public definition back to its exported fully qualified name.
buildExportSubstMap :: FilePath -> Book -> Either String SubstMap
buildExportSubstMap modulePath (Book defs _ _) =
  let modulePrefix = extractModuleName modulePath
  in case lastPathSegment modulePrefix of
       Nothing -> Left ("Error: invalid module path '" ++ modulePath ++ "'.")
       Just public ->
         let fqn = modulePrefix ++ "::" ++ public
         in case M.lookup fqn defs of
              Nothing -> Left ("Error: public definition '" ++ fqn ++ "' not found in module '" ++ modulePrefix ++ "'.")
              Just _  ->
                let entries =
                      [ (modulePrefix, fqn)
                      , (modulePrefix ++ "/" ++ public, fqn)
                      ]
                in Right (foldl' (\m (k, v) -> insertFunction k v m) mempty entries)

insertFunction :: Name -> Name -> SubstMap -> SubstMap
insertFunction alias target (SubstMap f p) = SubstMap (M.insert alias target f) p

insertPrefix :: Name -> Name -> SubstMap -> SubstMap
insertPrefix alias target (SubstMap f p) = SubstMap f (M.insert alias target p)

-- Book helpers ----------------------------------------------------------------

bookNames :: Book -> S.Set Name
bookNames (Book defs _ _) = S.fromList (M.keys defs)

bookDefs :: Book -> M.Map Name Defn
bookDefs (Book defs _ _) = defs

insertDefinition :: Book -> Name -> Defn -> Book
insertDefinition (Book defs names meta) name defn =
  let defs' = M.insert name defn defs
      names' = if name `elem` names then names else names ++ [name]
  in Book defs' names' meta

definitionDepOrigins :: Defn -> M.Map Name Span
definitionDepOrigins (_, term, typ) =
  let termDeps = collectDepSpans S.empty Nothing term
      typeDeps = collectDepSpans S.empty Nothing typ
  in M.union termDeps typeDeps

-- Importer state utilities ----------------------------------------------------

insertPending :: Name -> DepOrigin -> PendingDeps -> PendingDeps
insertPending name origin = M.insertWith keepExistingPending name origin

keepExistingPending :: DepOrigin -> DepOrigin -> DepOrigin
keepExistingPending _ old = old

markLoaded :: Name -> ImporterState -> ImporterState
markLoaded name st = st { isLoaded = S.insert name (isLoaded st) }

enqueueDependency :: Name -> DepOrigin -> ImporterState -> ImporterState
enqueueDependency name origin st =
  st { isPending = insertPending name origin (isPending st) }

mergeSubst :: SubstMap -> ImporterState -> ImporterState
mergeSubst subst st = st { isSubst = isSubst st <> subst }

-- Resolver --------------------------------------------------------------------

-- | Exhaust the pending dependency queue.
resolveAll :: ImporterState -> IO ImporterState
resolveAll st =
  case M.minViewWithKey (isPending st) of
    Nothing -> pure st
    Just ((dep, origin), rest) -> do
      let withoutDep = st { isPending = rest }
      resolved <- resolveDependency withoutDep dep origin
      resolveAll resolved

-- | Resolve a single dependency from the queue.
resolveDependency :: ImporterState -> Name -> DepOrigin -> IO ImporterState
resolveDependency st dep origin
  | dep `S.member` isLoaded st = pure st
  | otherwise =
      case applyNameSubst (isSubst st) dep of
        resolved | resolved /= dep -> pure (enqueueDependency resolved origin st)
        _ -> resolveConcreteDependency st dep origin

resolveConcreteDependency :: ImporterState -> Name -> DepOrigin -> IO ImporterState
resolveConcreteDependency st dep origin =
  case splitFQN dep of
    Just _  -> ensureDefinition origin dep st
    Nothing ->
      if not (looksLikeModule dep)
        then pure (markLoaded dep st)
        else do
          ensured <- ensureModuleFor origin dep st
          let resolved = applyNameSubst (isSubst ensured) dep
          if resolved == dep
            then throwImportError origin ("could not resolve reference '" ++ dep ++ "'.")
            else pure (enqueueDependency resolved origin ensured)

looksLikeModule :: Name -> Bool
looksLikeModule [] = False
looksLikeModule name = '/' `elem` name || isUpper (head name)

-- | Ensure the referenced definition exists in the working book, loading it if
-- needed.
ensureDefinition :: DepOrigin -> Name -> ImporterState -> IO ImporterState
ensureDefinition origin name st
  | name `S.member` isLoaded st = pure st
  | otherwise =
      case M.lookup name (bookDefs (isBook st)) of
        Just _ -> pure (markLoaded name st)
        Nothing ->
          case splitFQN name of
            Nothing -> throwImportError origin ("invalid fully qualified name '" ++ name ++ "'.")
            Just (modulePath, defName) -> do
              let publicName = lastPathSegment modulePath
                  cached = M.member modulePath (isModuleCache st)
              case publicName of
                Nothing -> throwImportError origin ("invalid module path '" ++ modulePath ++ "'.")
                Just pub | defName /= pub && not cached ->
                  throwImportError origin ("'" ++ name ++ "' is private to '" ++ modulePath ++ "'.")
                _ -> pure ()
              (modulePayload, st1) <- loadModule origin modulePath st
              let st2 = mergeSubst (snd modulePayload) st1
                  moduleBook = fst modulePayload
              case M.lookup name (bookDefs moduleBook) of
                Nothing -> throwImportError origin ("definition '" ++ name ++ "' not found in module '" ++ modulePath ++ "'.")
                Just defn -> do
                  let book' = insertDefinition (isBook st2) name defn
                      depOrigins = M.delete name (definitionDepOrigins defn)
                      subst' = isSubst st2
                      resolvedDeps =
                        [ (applyNameSubst subst' depName, Just sp)
                        | (depName, sp) <- M.toList depOrigins
                        , applyNameSubst subst' depName /= name
                        ]
                      alreadyKnown = S.union (bookNames book') (isLoaded st2)
                      filtered = filter (\(depName, _) -> depName `S.notMember` alreadyKnown) resolvedDeps
                      pending' = foldl' (\acc (depName, depSp) -> insertPending depName depSp acc) (isPending st2) filtered
                      stWithDef = st2 { isBook = book', isPending = pending' }
                  pure (markLoaded name stWithDef)

-- | Ensure the module exporting the given path is loaded and its export
-- substitution is merged into the state.
ensureModuleFor :: DepOrigin -> Name -> ImporterState -> IO ImporterState
ensureModuleFor origin modulePath st = do
  ((_, exportSubst), updated) <- loadModule origin modulePath st
  pure (mergeSubst exportSubst updated)

-- | Load a module from disk (or the cache) and return its rewritten book and
-- export substitution.
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
              combined = aliasSubst <> localSubst
              substituted = substituteRefsInBook combined book
          exportSubst <- case buildExportSubstMap posixPath substituted of
                           Left errMsg -> throwCompilationError errMsg
                           Right subst -> pure subst
          let cacheEntry = (substituted, exportSubst)
              cache' = M.insert modulePath cacheEntry (isModuleCache st)
          pure (cacheEntry, st { isModuleCache = cache' })

-- | Resolve a module path into POSIX and system paths, fetching from the index
-- when not available locally.
resolveModuleFile :: DepOrigin -> FilePath -> PkgIndex.IndexConfig -> String -> IO (String, FilePath)
resolveModuleFile origin root indexCfg modulePath = do
  let candidates = [modulePath ++ ".bend", modulePath ++ "/_.bend"]
  existing <- findExistingCandidate root candidates
  case existing of
    Just entry -> pure entry
    Nothing -> do
      fetchCandidates indexCfg candidates
      fetched <- findExistingCandidate root candidates
      case fetched of
        Just entry -> pure entry
        Nothing -> throwImportError origin ("unable to locate module '" ++ modulePath ++ "'.")

findExistingCandidate :: FilePath -> [FilePath] -> IO (Maybe (String, FilePath))
findExistingCandidate _ [] = pure Nothing
findExistingCandidate root (candidate:rest) = do
  let systemPath = fromPosixPath candidate
  exists <- doesFileExist (root </> systemPath)
  if exists
    then pure (Just (candidate, systemPath))
    else findExistingCandidate root rest

fetchCandidates :: PkgIndex.IndexConfig -> [FilePath] -> IO ()
fetchCandidates _ [] = pure ()
fetchCandidates cfg (candidate:rest) = do
  success <- attemptFetch cfg candidate
  unless success (fetchCandidates cfg rest)

attemptFetch :: PkgIndex.IndexConfig -> FilePath -> IO Bool
attemptFetch cfg candidate = do
  result <- PkgIndex.ensureFile cfg candidate
  case result of
    Left _  -> pure False
    Right () -> pure True

-- Path utilities --------------------------------------------------------------

normalizeRelativePath :: FilePath -> FilePath -> IO FilePath
normalizeRelativePath root path = do
  absRoot <- canonicalizePath root
  absPath <- canonicalizePath path
  let rel = FP.makeRelative absRoot absPath
  when (pathEscapesRoot rel) (throwCompilationError ("file '" ++ path ++ "' is outside BendRoot."))
  pure (toPosixPath rel)

pathEscapesRoot :: FilePath -> Bool
pathEscapesRoot p = ".." `elem` FP.splitDirectories p

splitFQN :: Name -> Maybe (String, String)
splitFQN name =
  case splitOn "::" name of
    [] -> Nothing
    [_] -> Nothing
    moduleName : rest -> Just (moduleName, intercalate "::" rest)

toPosixPath :: FilePath -> FilePath
toPosixPath path =
  let normalized = FP.normalise path
      replaced = map replaceSeparator normalized
  in dropWhile (== '/') (dropDotSlash replaced)

dropDotSlash :: String -> String
dropDotSlash ('.' : '/' : rest) = dropDotSlash rest
dropDotSlash other             = other

replaceSeparator :: Char -> Char
replaceSeparator c =
  if c == FP.pathSeparator then '/' else c

fromPosixPath :: FilePath -> FilePath
fromPosixPath p = FP.joinPath (splitOn "/" p)

-- Error helpers ---------------------------------------------------------------

throwImportError :: DepOrigin -> String -> IO a
throwImportError origin msg =
  case origin of
    Just sp -> throwIO (BendException (ImportError sp msg))
    Nothing -> throwIO (BendException (CompilationError msg))

throwCompilationError :: String -> IO a
throwCompilationError msg = throwIO (BendException (CompilationError msg))
