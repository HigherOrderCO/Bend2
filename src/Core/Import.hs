{-./Type.hs-}

module Core.Import (autoImport, autoImportWithExplicit) where

import Data.List (intercalate, isInfixOf, isSuffixOf, isPrefixOf, sort)
import Data.List.Split (splitOn)
import Data.Maybe (fromMaybe)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import System.Directory (doesFileExist, doesDirectoryExist, listDirectory)
import System.Exit (exitFailure)
import System.FilePath ((</>))
import qualified System.FilePath as FP
import System.IO (hPutStrLn, stderr)
import Core.Type
import Core.Deps
import Core.Parse.Book (doParseBook)
import Core.Parse.Parse (ParserState(..), Import(..))
import qualified Package.Index as PkgIndex
import qualified Data.Map.Strict as M

-- Substitution types and functions
data SubstMap = SubstMap
  { functionMap :: M.Map Name Name  -- For resolving Ref terms (function calls)
  , enumMap     :: M.Map Name Name  -- For resolving Sym terms (enum constructors)
  } deriving (Show, Eq)

-- Helper functions for SubstMap operations
emptySubstMap :: SubstMap
emptySubstMap = SubstMap M.empty M.empty

unionSubstMap :: SubstMap -> SubstMap -> SubstMap
unionSubstMap (SubstMap f1 e1) (SubstMap f2 e2) =
  SubstMap (M.union f1 f2) (M.union e1 e2)

insertFunction :: Name -> Name -> SubstMap -> SubstMap
insertFunction k v (SubstMap fMap eMap) = SubstMap (M.insert k v fMap) eMap


-- | Substitute aliases in enum names
-- For example: "some::B::X" with {"some" -> "B::B"} becomes "B::B::X"  
-- Also handles: "B::X" with {"B" -> "B::B"} becomes "B::B::X"
-- The substitution maps module aliases and imported names to fully qualified names
substituteInEnumName :: SubstMap -> String -> String
substituteInEnumName subst name =
  -- If the name is already a fully qualified enum (Module::Type::Enum), don't substitute
  -- This prevents incorrect substitution when module name conflicts with function names
  let parts = splitEnumName name
      eMap = enumMap subst
      -- A fully qualified enum has at least 3 parts and contains ::
  in if length parts >= 3 && "::" `isInfixOf` name
  then name
  else case parts of
    [single] ->
      -- No :: found, check if the whole name needs substitution
      case M.lookup single eMap of
        Just replacement -> replacement
        Nothing -> single
    [typeName, enumName] ->
      -- Two parts: could be Type::Enum
      -- Check if typeName is in substitution map (from selective import)
      case M.lookup typeName eMap of
        Just replacement ->
          -- replacement is like "B::B" for "from B import B"
          -- Append the enum name
          replacement ++ "::" ++ enumName
        Nothing -> 
          -- No substitution needed, keep original
          name
    parts@(prefix:typeName:rest) ->
      -- Three or more parts: Module::Type::Enum or similar
      -- Check if prefix is an alias that needs substitution
      case M.lookup prefix eMap of
        Just replacement ->
          -- replacement is like "B::B" for "import B as some"
          -- We need to check if prefix::typeName together form the qualified type
          -- If replacement already contains the type name, use it directly
          if "::" `isInfixOf` replacement && not ("::" `isSuffixOf` replacement)
          then
            -- replacement is already a qualified name like "B::B"
            -- Just append the enum name
            if null rest
            then replacement  -- No enum, just the type
            else replacement ++ "::" ++ intercalate "::" rest  -- Add enum
          else
            -- replacement is just a module name, build the full path
            intercalate "::" (replacement : typeName : rest)
        Nothing -> 
          -- Check if prefix::typeName together might be in the substitution map
          let prefixWithType = prefix ++ "::" ++ typeName
          in case M.lookup prefixWithType eMap of
            Just replacement ->
              -- Found a match for the combined prefix::type
              if null rest
              then replacement
              else replacement ++ "::" ++ intercalate "::" rest
            Nothing ->
              -- No substitution needed, keep original
              name
    _ -> name
  where
    -- Split on "::" to get components
    splitEnumName :: String -> [String]
    splitEnumName s = 
      case break (== ':') s of
        (part, ':':':':rest) -> part : splitEnumName rest
        (part, "") -> [part]
        _ -> [s]

-- | Apply a substitution map to all Ref, Var, and Sym terms in a term
substituteRefs :: SubstMap -> Term -> Term
substituteRefs subst = go S.empty
  where
    fMap = functionMap subst
    go bound term = case term of
      Ref k i ->
        case M.lookup k fMap of
          Just newName -> Ref newName i
          Nothing -> Ref k i

      -- Handle binding constructs
      Var k i ->
        if k `S.member` bound
        then Var k i  -- It's a bound variable, don't substitute
        else case M.lookup k fMap of
          Just newName -> Var newName i  -- It's a free variable, substitute it
          Nothing -> Var k i
      
      -- Handle enum names that might contain aliases
      Sym name -> Sym (substituteInEnumName subst name)
      
      Sub t -> Sub (go bound t)
      Fix k f -> Fix k (\v -> go (S.insert k bound) (f v))
      Let k t v f -> Let k (fmap (go bound) t) (go bound v) (\u -> go (S.insert k bound) (f u))
      Use k v f -> Use k (go bound v) (\u -> go (S.insert k bound) (f u))
      Set -> Set
      Chk x t -> Chk (go bound x) (go bound t)
      Tst x -> Tst (go bound x)
      Emp -> Emp
      EmpM -> EmpM
      Uni -> Uni
      One -> One
      UniM f -> UniM (go bound f)
      Bit -> Bit
      Bt0 -> Bt0
      Bt1 -> Bt1
      BitM f t -> BitM (go bound f) (go bound t)
      Nat -> Nat
      Zer -> Zer
      Suc n -> Suc (go bound n)
      NatM z s -> NatM (go bound z) (go bound s)
      Lst t -> Lst (go bound t)
      Nil -> Nil
      Con h t -> Con (go bound h) (go bound t)
      LstM n c -> LstM (go bound n) (go bound c)
      Enu cs -> Enu cs
      EnuM cs d -> EnuM (map (\(s, t) -> (s, go bound t)) cs) (go bound d)
      Num n -> Num n
      Val v -> Val v
      Op2 op a b -> Op2 op (go bound a) (go bound b)
      Op1 op a -> Op1 op (go bound a)
      Sig a b -> Sig (go bound a) (go bound b)
      Tup a b -> Tup (go bound a) (go bound b)
      SigM f -> SigM (go bound f)
      All a b -> All (go bound a) (go bound b)
      Lam k t f -> Lam k (fmap (go bound) t) (\u -> go (S.insert k bound) (f u))
      App f x -> 
        let newF = go bound f
            newX = go bound x
            result = App newF newX
        in result
      Eql t a b -> Eql (go bound t) (go bound a) (go bound b)
      Rfl -> Rfl
      EqlM f -> EqlM (go bound f)
      Met n t ctx -> Met n (go bound t) (map (go bound) ctx)
      Era -> Era
      Sup l a b -> Sup (go bound l) (go bound a) (go bound b)
      SupM l f -> SupM (go bound l) (go bound f)
      Loc sp t -> Loc sp (go bound t)
      Log s x -> Log (go bound s) (go bound x)
      Pri p -> Pri p
      Rwt e f -> Rwt (go bound e) (go bound f)
      Pat s m c -> Pat (map (go bound) s) 
                      (map (\(n, t) -> (n, go bound t)) m) 
                      (map (\(ps, b) -> (map (go bound) ps, go bound b)) c)
      Frk l a b -> Frk (go bound l) (go bound a) (go bound b)

-- | Apply substitution to a book
substituteRefsInBook :: SubstMap -> Book -> Book
substituteRefsInBook subst (Book defs names) = 
  Book (M.map (substituteRefsInDefn subst) defs) names
  where
    substituteRefsInDefn :: SubstMap -> Defn -> Defn
    substituteRefsInDefn s (inj, term, typ) = 
      let newTerm = substituteRefs s term
          newTyp = substituteRefs s typ
      in (inj, newTerm, newTyp)

-- Public API

autoImport :: FilePath -> Book -> IO Book
autoImport root book = do
  result <- importAll root book
  case result of
    Left err -> do
      hPutStrLn stderr $ "Error: " ++ err
      exitFailure
    Right b -> pure b

autoImportWithExplicit :: FilePath -> Book -> ParserState -> IO Book  
autoImportWithExplicit root book parserState = do
  result <- importAllWithExplicit root book parserState
  case result of
    Left err -> do
      hPutStrLn stderr $ "Error: " ++ err
      exitFailure
    Right b -> pure b

-- Internal

data ImportResult 
  = ImportSuccess Book SubstMap  -- ^ Successful import with book and substitution map
  | ImportFailed String          -- ^ Import failed with error message
  deriving (Show)

data ImportState = ImportState
  { stVisited :: S.Set FilePath      -- files already parsed (cycle/dup prevention)
  , stLoaded  :: S.Set Name          -- names we consider resolved/loaded
  , stBook    :: Book                -- accumulated book
  , stSubstMap :: SubstMap           -- substitution map for reference resolution
  , stCurrentFile :: FilePath        -- current file being processed
  , stModuleImports :: S.Set String  -- modules imported via "import Module" (blocks auto-import for their definitions)
  , stAliases :: M.Map String String -- alias mapping: "NatOps" -> "Nat/add"
  }

importAll :: FilePath -> Book -> IO (Either String Book)
importAll currentFile base = do
  let -- Build substitution map for local definitions
      localSubstMap = buildLocalSubstMap currentFile base
      -- Apply local substitutions to the base book first
      substitutedBase = substituteRefsInBook localSubstMap base
      initial = ImportState
        { stVisited = S.empty
        , stLoaded  = bookNames substitutedBase
        , stBook    = substitutedBase
        , stSubstMap = localSubstMap
        , stCurrentFile = currentFile
        , stModuleImports = S.empty
        , stAliases = M.empty
        }
      -- Collect dependencies from the substituted book
      pending0 = getBookDeps substitutedBase
  res <- importLoop initial pending0
  case res of
    Left err -> pure (Left err)
    Right st -> do
      -- Apply substitution map to the final book
      let substMap = stSubstMap st
          finalBook = substituteRefsInBook substMap (stBook st)
      -- FQN system successfully implemented
      pure (Right finalBook)

importAllWithExplicit :: FilePath -> Book -> ParserState -> IO (Either String Book)
importAllWithExplicit currentFile base parserState = do
  -- Process explicit imports using cascading resolution (local then external)
  explicitResult <- processExplicitImports parserState
  case explicitResult of
    Left err -> pure (Left err)
    Right (explicitBook, explicitSubstMap) -> do
      let -- Build substitution map for local definitions
          localSubstMap = buildLocalSubstMap currentFile base
          -- Combine explicit and local substitution maps (explicit takes precedence)
          combinedSubstMap = unionSubstMap explicitSubstMap localSubstMap
          -- Apply combined substitutions to both books
          substitutedBase = substituteRefsInBook combinedSubstMap base
          substitutedExplicit = substituteRefsInBook combinedSubstMap explicitBook
          mergedBook = mergeBooks substitutedBase substitutedExplicit
          initial = ImportState
            { stVisited = S.empty
            , stLoaded  = S.union (bookNames substitutedBase) (bookNames substitutedExplicit)
            , stBook    = mergedBook
            , stSubstMap = combinedSubstMap
            , stCurrentFile = currentFile
            , stModuleImports = S.empty -- Will be populated from parsed imports
            , stAliases = M.empty       -- Will be populated from parsed imports
            }
          -- Collect dependencies from the substituted merged book
          pending0 = getBookDeps mergedBook
      res <- importLoop initial pending0
      case res of
        Left err -> pure (Left err)
        Right st -> do
          -- Apply substitution map to the final book
          let substMap = stSubstMap st
              finalBook = substituteRefsInBook substMap (stBook st)
          pure (Right finalBook)


-- | Process explicit imports using cascading resolution (local first, then external)
processExplicitImports :: ParserState -> IO (Either String (Book, SubstMap))
processExplicitImports parserState = do
  let imports = parsedImports parserState
  results <- mapM resolveCascadingImport imports
  
  -- Check for errors
  let errors = [err | ImportFailed err <- results]
  if not (null errors)
    then pure (Left $ unlines errors)
    else do
      let successes          = [result | ImportSuccess book substMap <- results, result <- [(book, substMap)]]
          (books, substMaps) = unzip successes
          combinedBook       = foldr mergeBooks (Book M.empty []) books
          combinedSubstMap   = foldr unionSubstMap emptySubstMap substMaps
      pure (Right (combinedBook, combinedSubstMap))

-- | Cascading resolution: try local first, then external
resolveCascadingImport :: Import -> IO ImportResult
resolveCascadingImport imp = do
  localResult <- resolveLocalImport imp
  case localResult of
    ImportSuccess book substMap -> pure (ImportSuccess book substMap)
    ImportFailed localErr       -> do
      externalResult <- resolveExternalImport imp
      case externalResult of
        ImportSuccess book substMap -> pure (ImportSuccess book substMap)
        ImportFailed externalErr    -> pure $ ImportFailed $ "Failed to resolve import: " ++ localErr ++ " (local), " ++ externalErr ++ " (external)"

-- | Try to resolve import locally (in local files or bend_packages)
resolveLocalImport :: Import -> IO ImportResult
resolveLocalImport (ModuleImport modulePath maybeAlias) = do
  case maybeAlias of
    Nothing    -> do
      -- Regular module import: import and return the book
      result <- processModuleImport modulePath
      case result of
        Left err                             -> pure (ImportFailed err)
        Right (book, _substMap, _actualPath) -> pure (ImportSuccess book emptySubstMap)

    Just alias -> do
      -- Aliased module import: import the module and create alias mappings
      result <- processModuleImport modulePath
      case result of
        Left err                            -> pure (ImportFailed err)
        Right (book, _substMap, actualPath) -> do
          let Book defs _ = book
              possibleFQNs = M.keys defs
              -- Create mappings for ALL functions in the module
              -- e.g., "tst::mul2" -> "examples/main::mul2", "tst::id" -> "examples/main::id", etc.
              modulePrefix = takeBaseName' actualPath
              aliasEntries = [(alias ++ "::" ++ dropModulePrefix modulePrefix fqn, fqn) | fqn <- possibleFQNs]
              
              -- For external imports, also check if there's a main function that matches the original module path
              -- If so, create a direct alias (e.g., "external_add" -> "Nat/add")
              -- Extract the main function name from the original import path
              -- "Lorenzobattistela/bendLib/Nat/add" -> "Nat/add"
              -- "fixme/add_for_import" -> "fixme/add_for_import" (local import)
              extractMainFunctionName path =
                let parts = splitOn "/" path
                in case length parts of
                     1 -> path  -- Single part: "add" -> "add"
                     2 -> path  -- Two parts: "fixme/add_for_import" -> "fixme/add_for_import"
                     _ -> intercalate "/" (drop 2 parts)  -- External: "user/lib/Nat/add" -> "Nat/add"

              mainFunctionName = extractMainFunctionName modulePath
              mainFunctionFQN = modulePrefix ++ "::" ++ mainFunctionName  
              directAliasEntries = if not (null mainFunctionName) && mainFunctionFQN `elem` possibleFQNs
                                   then [(alias, mainFunctionFQN)]
                                   else []
                                  
              substMap = SubstMap (M.fromList (aliasEntries ++ directAliasEntries)) M.empty
              
          pure (ImportSuccess book substMap)
          where
            -- Drop module prefix from FQN: "examples/main::mul2" -> "mul2"
            dropModulePrefix :: String -> String -> String
            dropModulePrefix prefix fqn = 
              let expectedPrefix = prefix ++ "::"
              in if expectedPrefix `isPrefixOf` fqn
                 then drop (length expectedPrefix) fqn
                 else fqn

resolveLocalImport (SelectiveImport modulePath names) = do
  result <- processSelectiveImport modulePath names
  case result of
    Left err               -> pure (ImportFailed err)
    Right (book, substMap) -> pure (ImportSuccess book substMap)

-- | Try to resolve import externally (via package index)
resolveExternalImport :: Import -> IO ImportResult
resolveExternalImport (ModuleImport modulePath maybeAlias) = do
  -- Try to parse as package index format: owner/package/path/to/definition
  case splitOn "/" modulePath of
    (owner:package:pathParts) | length pathParts >= 1 -> do
      -- Try to fetch from package index
      indexConfig <- PkgIndex.defaultIndexConfig
      let importStr = modulePath
      result <- PkgIndex.importDefinition indexConfig importStr maybeAlias
      case result of
        Left err -> pure (ImportFailed err)
        Right resolved -> do
          -- Use the actual file path returned by the API (includes version)
          let actualFilePath = PkgIndex.rrFile resolved
          resolveLocalImport (ModuleImport actualFilePath maybeAlias)

    _ -> pure (ImportFailed $ "Invalid external import format (expected owner/package/path): " ++ modulePath)

resolveExternalImport (SelectiveImport modulePath nameAliases) = do
  -- First try to import the module externally
  case splitOn "/" modulePath of
    (owner:package:pathParts) | length pathParts >= 1 -> do
      indexConfig <- PkgIndex.defaultIndexConfig
      let importStr = modulePath
      result <- PkgIndex.importDefinition indexConfig importStr Nothing
      case result of
        Left err       -> pure (ImportFailed err)
        Right resolved -> do
          -- Use the actual file path returned by the API (includes version)
          let actualFilePath = PkgIndex.rrFile resolved
          resolveLocalImport (SelectiveImport actualFilePath nameAliases)

    _ -> pure (ImportFailed $ "Invalid external import format (expected owner/package/path): " ++ modulePath)

-- | Process a single module import: import Nat/add
processModuleImport :: String -> IO (Either String (Book, SubstMap, String))
processModuleImport modulePath = do
  candidates <- generateImportPaths modulePath
  mFound <- firstExisting candidates
  case mFound of
    Just path -> do
      content <- readFile path
      case doParseBook path content of
        Left err        -> pure $ Left $ "Failed to parse " ++ path ++ ": " ++ err
        Right (book, _) -> do
          -- Build local substitution map for the imported file to resolve internal references
          let localSubstMap = buildLocalSubstMap path book
          -- Apply substitutions to resolve internal references
          let substitutedBook = substituteRefsInBook localSubstMap book
          pure $ Right (substitutedBook, emptySubstMap, path)
    Nothing -> pure $ Left $ "Cannot find module: " ++ modulePath

-- | Process a selective import: from Nat/add import name1 [as alias1], name2 [as alias2], ...
processSelectiveImport :: String -> [(String, Maybe String)] -> IO (Either String (Book, SubstMap))
processSelectiveImport modulePath nameAliases = do
  candidates <- generateImportPaths modulePath
  mFound <- firstExisting candidates
  case mFound of
    Just path -> do
      content <- readFile path
      case doParseBook path content of
        Left err        -> pure $ Left $ "Failed to parse " ++ path ++ ": " ++ err
        Right (book, _) -> do
          let modulePrefix = takeBaseName' path
              Book defs defNames = book
              -- Extract just the function names for filtering
              functionNames = map fst nameAliases
              -- Filter book to only include selected functions
              selectedFQNs = [modulePrefix ++ "::" ++ name | name <- functionNames]
              filteredDefs = M.filterWithKey (\fqn _ -> fqn `elem` selectedFQNs) defs
              filteredNames = filter (`elem` selectedFQNs) defNames
              filteredBook = Book filteredDefs filteredNames
              -- Build substitution map with aliases
              substEntries = [(alias, modulePrefix ++ "::" ++ name) 
                             | (name, maybeAlias) <- nameAliases
                             , let alias = fromMaybe name maybeAlias]
              substMap = SubstMap (M.fromList substEntries) M.empty
          pure $ Right (filteredBook, substMap)
    Nothing -> pure $ Left $ "Cannot find module for selective import: " ++ modulePath


importLoop :: ImportState -> S.Set Name -> IO (Either String ImportState)
importLoop st pending =
  case S.minView pending of
    Nothing -> pure (Right st)
    Just (ref, rest)
      | ref `S.member` stLoaded st -> importLoop st rest
      | otherwise -> do
          r <- resolveRef st ref
          case r of
            Left err   -> pure (Left err)
            Right st'  -> do
              -- Apply current substitution before recomputing deps to avoid infinite loops
              let substBook = substituteRefsInBook (stSubstMap st') (stBook st')
                  deps' = getBookDeps substBook
                  next  = S.union rest deps'
              importLoop st' next

-- | Resolve a reference by building substitution map entry
resolveRef :: ImportState -> Name -> IO (Either String ImportState)
resolveRef st refName = do
  -- First check if it's already in the substitution map
  if refName `M.member` functionMap (stSubstMap st)
    then pure (Right st)
    else do
      -- Check if this is an alias reference (alias::name)
      case break (== ':') refName of
        (aliasName, ':':':':actualName) | aliasName `M.member` stAliases st -> do
          -- Resolve alias reference
          let modulePath = stAliases st M.! aliasName
              qualifiedRef = modulePath ++ "::" ++ actualName
              newSubstMap = insertFunction refName qualifiedRef (stSubstMap st)
              newLoaded = S.insert refName (stLoaded st)
          pure $ Right st { stSubstMap = newSubstMap, stLoaded = newLoaded }
        _ -> do
          -- Regular reference resolution
          -- Check if it's a local reference (qualified version exists in any loaded module)
          let Book defs _ = stBook st
              -- Look for any FQN that ends with "::refName"
              matchingFQNs = filter (\fqn -> ("::" ++ refName) `isSuffixOf` fqn) (M.keys defs)
          
          case matchingFQNs of
            [fqn] -> do
              -- Extract module prefix and function name from FQN
              let modulePrefix = takeWhile (/= ':') fqn
                  functionName = drop (length modulePrefix + 2) fqn  -- Skip "module::"
              
              -- Check if this FQN is accessible:
              -- 1. If it's already in the substitution map, it was explicitly imported
              if refName `M.member` functionMap (stSubstMap st)
                then do
                  -- Already resolved, use existing mapping
                  pure $ Right st
              -- 2. Check if it's from a selective import (should already be in substMap from processExplicitImports)
              -- 3. For auto-import to work, the function name must match the module name
              else if refName == modulePrefix
                then do
                  -- Auto-import is allowed when function name matches module name
                  let newSubstMap = insertFunction refName fqn (stSubstMap st)
                      newLoaded = S.insert refName (stLoaded st)
                  pure $ Right st { stSubstMap = newSubstMap, stLoaded = newLoaded }
                else do
                  -- Function name doesn't match module name, auto-import not allowed
                  -- Try to load it as a new module
                  loadRef st refName
            [] -> do
              -- No matches - try auto-import
              loadRef st refName
            multiple -> do
              -- Multiple matches - ambiguous reference error
              pure $ Left $ "Ambiguous reference '" ++ refName ++ "' could refer to: " ++ show multiple
  where
    takeBaseName :: FilePath -> String
    takeBaseName path = 
      if ".bend" `isSuffixOf` path
         then take (length path - 5) path  -- Remove .bend extension but keep full path
         else path

takeBaseName' :: FilePath -> String
takeBaseName' path = 
  let withoutBend = if ".bend" `isSuffixOf'` path
                    then take (length path - 5) path  -- Remove .bend extension
                    else path
      -- Also remove /_ suffix if present (for files like Term/_.bend)
      withoutUnderscore = if "/_" `isSuffixOf'` withoutBend
                          then take (length withoutBend - 2) withoutBend  -- Remove /_
                          else withoutBend
  in withoutUnderscore
  where
    isSuffixOf' :: Eq a => [a] -> [a] -> Bool
    isSuffixOf' suffix str = suffix == drop (length str - length suffix) str

-- | Build substitution map for local definitions
-- For each definition in the book with FQN "module::name", 
-- add a mapping from "name" to "module::name"
-- Also handles enum names: "module::Type::Enum" -> "Enum" maps to full FQN
buildLocalSubstMap :: FilePath -> Book -> SubstMap
buildLocalSubstMap currentFile (Book defs _) =
  let filePrefix = takeBaseName' currentFile ++ "::"
      localDefs = M.filterWithKey (\k _ -> filePrefix `isPrefixOf` k) defs

      -- Separate function mappings from enum mappings
      extractMappings fqn defn =
        let withoutFilePrefix = drop (length filePrefix) fqn
            parts = splitOnDoubleColon withoutFilePrefix
            (functionMappings, enumMappings) = case parts of
              -- Regular function: ["add"] -> "add" -> "examples/main::add"
              [name] -> ([(name, fqn)], [])
              -- Enum constructor: ["WTreeTag", "WLeaf"] ->
              -- Function map gets nothing, enum map gets both qualified and unqualified
              [typeName, enumName] ->
                ([], [(withoutFilePrefix, fqn), (enumName, fqn)])
              -- Fallback: assume it's a function
              _ -> ([(withoutFilePrefix, fqn)], [])
            -- Extract additional enum names from type definitions
            additionalEnumMappings = extractEnumsFromDefn defn
        in (functionMappings, enumMappings ++ additionalEnumMappings)

      -- Extract enum names from a definition's term
      extractEnumsFromDefn :: Defn -> [(String, String)]
      extractEnumsFromDefn (_, term, _) = extractEnumsFromTerm term

      -- Extract enum names from a term (look for Enu constructors)
      extractEnumsFromTerm :: Term -> [(String, String)]
      extractEnumsFromTerm term = case term of
        -- Look for enum types which contain fully qualified enum names
        Sig (Enu tags) _ -> [(takeUnqualified tag, tag) | tag <- tags]
        -- Recursively search in other term constructors
        Lam _ _ f -> extractEnumsFromTerm (f (Var "dummy" 0))
        App f x -> extractEnumsFromTerm f ++ extractEnumsFromTerm x
        Sig a b -> extractEnumsFromTerm a ++ extractEnumsFromTerm b
        All a b -> extractEnumsFromTerm a ++ extractEnumsFromTerm b
        _ -> []

      -- Extract unqualified name from a fully qualified enum name
      -- "examples/main::WTreeTag::WLeaf" -> "WLeaf"
      takeUnqualified :: String -> String
      takeUnqualified fqn =
        case reverse (splitOnDoubleColon fqn) of
          (lastPart:_) -> lastPart
          [] -> fqn

      -- Split on "::" separator
      splitOnDoubleColon :: String -> [String]
      splitOnDoubleColon s =
        case findDoubleColon s of
          Nothing -> [s]
          Just (before, after) -> before : splitOnDoubleColon after

      findDoubleColon :: String -> Maybe (String, String)
      findDoubleColon s = findDoubleColon' s ""
        where
          findDoubleColon' [] _ = Nothing
          findDoubleColon' (':':':':rest) acc = Just (reverse acc, rest)
          findDoubleColon' (c:rest) acc = findDoubleColon' rest (c:acc)

      -- Collect all mappings and separate them
      allMappings = map (\(fqn, defn) -> extractMappings fqn defn) (M.toList localDefs)
      (functionMappings, enumMappings) = foldl
        (\(fs, es) (f, e) -> (fs ++ f, es ++ e))
        ([], [])
        allMappings

      functionMap = M.fromList functionMappings
      enumMap = M.fromList enumMappings
  in SubstMap functionMap enumMap

loadRef :: ImportState -> Name -> IO (Either String ImportState)
loadRef st refName = do
  candidates <- generateImportPaths refName
  let visitedHit = any (`S.member` stVisited st) candidates
  if visitedHit
    then
      -- Already visited one of the candidate files earlier (cycle/dup); consider it loaded.
      pure $ Right st { stLoaded = S.insert refName (stLoaded st) }
    else do
      mFound <- firstExisting candidates
      case mFound of
        Just path -> do
          content <- readFile path
          case doParseBook path content of
            Left perr -> pure $ Left $ "Failed to parse " ++ path ++ ": " ++ perr
            Right (imported, _) -> do
              -- Build local substitution map for the imported file
              let importedLocalSubstMap = buildLocalSubstMap path imported
                  -- Apply local substitutions to the imported book
                  substitutedImported = substituteRefsInBook importedLocalSubstMap imported
                  visited' = S.insert path (stVisited st)
                  merged   = mergeBooks (stBook st) substitutedImported
                  loaded'  = S.union (stLoaded st) (bookNames substitutedImported)
                  -- Auto-import should only work if refName matches the module name
                  importFilePrefix = takeBaseName' path ++ "::"
                  importQualified = importFilePrefix ++ refName
                  moduleName = takeBaseName' path
                  -- With our change, Term/_.bend now gives moduleName "Term" (not "Term/_")
                  -- So definitions are Term::foo, not Term/_::foo
                  Book importedDefs _ = substitutedImported
                  shouldAddMapping = refName == moduleName && importQualified `M.member` importedDefs
                  newSubstMap = if shouldAddMapping
                              then insertFunction refName importQualified (stSubstMap st)
                              else stSubstMap st
              pure $ Right st { stVisited = visited', stLoaded = loaded', stBook = merged, stSubstMap = newSubstMap }
        Nothing -> do
          isDir <- doesDirectoryExist refName
          if isDir
            then
              pure $ Left $ unlines
                [ "Import error:"
                , "  Found directory for '" ++ refName ++ "', but expected module file was not found."
                , "  Missing file: " ++ (refName </> "_.bend")
                ]
            else
              if hasSlash refName
                then
                  let tried = intercalate ", " candidates
                  in pure $ Left $ "Import error: Could not find file for '" ++ refName ++ "'. Tried: " ++ tried
                else
                  -- Non-hierarchical names may be provided by the environment; skip without error.
                  pure $ Right st { stLoaded = S.insert refName (stLoaded st) }

firstExisting :: [FilePath] -> IO (Maybe FilePath)
firstExisting [] = pure Nothing
firstExisting (p:ps) = do
  ok <- doesFileExist p
  if ok then pure (Just p) else firstExisting ps

-- Prefer Foo/Bar/_.bend if Foo/Bar/ is a directory; otherwise Foo/Bar.bend
-- Also check in bend_packages directory
generateImportPaths :: Name -> IO [FilePath]
generateImportPaths name = do
  isDir <- doesDirectoryExist name
  let localPath = if isDir then name </> "_.bend" else name ++ ".bend"
  
  -- Check if bend_packages directory exists
  hasBendPackages <- doesDirectoryExist "bend_packages"
  if hasBendPackages
    then do
      -- Also check in bend_packages
      let pkgPath = "bend_packages" </> name
      isPkgDir <- doesDirectoryExist pkgPath
      let bendPkgPath = if isPkgDir then pkgPath </> "_.bend" else "bend_packages" </> (name ++ ".bend")
      pure [localPath, bendPkgPath]
    else
      pure [localPath]

hasSlash :: String -> Bool
hasSlash = any (== '/')

bookNames :: Book -> S.Set Name
bookNames (Book defs _) = S.fromList (M.keys defs)

mergeBooks :: Book -> Book -> Book
mergeBooks (Book defs1 names1) (Book defs2 names2) =
  Book (M.union defs1 defs2) (names1 ++ filter (`notElem` names1) names2)




