{-./Type.hs-}

module Core.Import (autoImport, autoImportWithExplicit) where

import Data.List (intercalate)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import System.Directory (doesFileExist, doesDirectoryExist)
import System.Exit (exitFailure)
import System.FilePath ((</>))
import System.IO (hPutStrLn, stderr)

import Core.Type
import Core.Deps
import Core.Parse.Book (doParseBook)
import Core.Parse.Parse (ParserState(..))
import qualified Data.Map.Strict as M

-- Substitution types and functions
type SubstMap = M.Map Name Name

-- | Apply a substitution map to all Ref and Var terms in a term
substituteRefs :: SubstMap -> Term -> Term
substituteRefs subst = go S.empty
  where
    go bound term = case term of
      Ref k i -> 
        case M.lookup k subst of
          Just newName -> Ref newName i
          Nothing -> Ref k i
      
      -- Handle binding constructs  
      Var k i -> 
        if k `S.member` bound 
        then Var k i  -- It's a bound variable, don't substitute
        else case M.lookup k subst of
          Just newName -> Var newName i  -- It's a free variable, substitute it
          Nothing -> Var k i
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
      Sym s -> Sym s
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

data ImportState = ImportState
  { stVisited :: S.Set FilePath   -- files already parsed (cycle/dup prevention)
  , stLoaded  :: S.Set Name       -- names we consider resolved/loaded
  , stBook    :: Book             -- accumulated book
  , stSubstMap :: SubstMap        -- substitution map for reference resolution
  , stCurrentFile :: FilePath     -- current file being processed
  , stModuleImports :: S.Set String -- modules imported via "import Module" (blocks auto-import for their definitions)
  , stAliases :: M.Map String String -- alias mapping: "NatOps" -> "Nat/add"
  }

importAll :: FilePath -> Book -> IO (Either String Book)
importAll currentFile base = do
  let initial = ImportState
        { stVisited = S.empty
        , stLoaded  = bookNames base
        , stBook    = base
        , stSubstMap = M.empty
        , stCurrentFile = currentFile
        , stModuleImports = S.empty
        , stAliases = M.empty
        }
      pending0 = getBookDeps base
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
  -- First process explicit imports to build initial substitution map
  explicitResult <- processExplicitImports parserState
  case explicitResult of
    Left err -> pure (Left err)
    Right (explicitBook, explicitSubstMap) -> do
      let mergedBook = mergeBooks base explicitBook
          initial = ImportState
            { stVisited = S.empty
            , stLoaded  = S.union (bookNames base) (bookNames explicitBook)
            , stBook    = mergedBook
            , stSubstMap = explicitSubstMap
            , stCurrentFile = currentFile
            , stModuleImports = S.fromList (moduleImports parserState)
            , stAliases = M.fromList (aliasImports parserState)
            }
          pending0 = getBookDeps mergedBook
      res <- importLoop initial pending0
      case res of
        Left err -> pure (Left err)
        Right st -> do
          -- Apply substitution map to the final book
          let substMap = stSubstMap st
              finalBook = substituteRefsInBook substMap (stBook st)
          pure (Right finalBook)

-- | Process explicit imports from parser state
processExplicitImports :: ParserState -> IO (Either String (Book, SubstMap))
processExplicitImports parserState = do
  -- Process module imports: import Nat/add
  moduleResults <- mapM processModuleImport (moduleImports parserState)
  -- Process selective imports: from Nat/add import Nat/add, Nat/add/go  
  selectiveResults <- mapM (uncurry processSelectiveImport) (selectiveImports parserState)
  -- Process alias imports: import Nat/add as NatOps
  aliasResults <- mapM (uncurry processAliasImport) (aliasImports parserState)
  
  -- Combine results
  case sequence (moduleResults ++ selectiveResults ++ aliasResults) of
    Left err -> pure (Left err)
    Right results -> do
      let (books, substMaps) = unzip results
          combinedBook = foldr mergeBooks (Book M.empty []) books
          combinedSubstMap = M.unions substMaps
      pure (Right (combinedBook, combinedSubstMap))

-- | Process a single module import: import Nat/add
processModuleImport :: String -> IO (Either String (Book, SubstMap))
processModuleImport modulePath = do
  candidates <- generateImportPaths modulePath
  mFound <- firstExisting candidates
  case mFound of
    Just path -> do
      content <- readFile path
      case doParseBook path content of
        Left err -> pure $ Left $ "Failed to parse " ++ path ++ ": " ++ err
        Right book -> do
          -- For module imports, we don't add names to substitution map
          -- They are accessed via qualified syntax (module::name)
          pure $ Right (book, M.empty)
    Nothing -> pure $ Left $ "Cannot find module: " ++ modulePath

-- | Process a selective import: from Nat/add import [Nat/add, Nat/add/go]
processSelectiveImport :: String -> [String] -> IO (Either String (Book, SubstMap))
processSelectiveImport modulePath names = do
  candidates <- generateImportPaths modulePath
  mFound <- firstExisting candidates
  case mFound of
    Just path -> do
      content <- readFile path
      case doParseBook path content of
        Left err -> pure $ Left $ "Failed to parse " ++ path ++ ": " ++ err
        Right book -> do
          let modulePrefix = takeBaseName' path
          -- Build substitution map for selected names
          let substEntries = [(name, modulePrefix ++ "::" ++ name) | name <- names]
              substMap = M.fromList substEntries
          pure $ Right (book, substMap)
    Nothing -> pure $ Left $ "Cannot find module for selective import: " ++ modulePath

-- | Process an alias import: import Nat/add as NatOps
processAliasImport :: String -> String -> IO (Either String (Book, SubstMap))
processAliasImport alias modulePath = do
  candidates <- generateImportPaths modulePath
  mFound <- firstExisting candidates
  case mFound of
    Just path -> do
      content <- readFile path
      case doParseBook path content of
        Left err -> pure $ Left $ "Failed to parse " ++ path ++ ": " ++ err
        Right book -> do
          -- For alias imports, we don't build a substitution map here
          -- Instead, we handle alias::name resolution during import resolution
          -- Just load the module and return empty substitution map
          pure $ Right (book, M.empty)
    Nothing -> pure $ Left $ "Cannot find module for alias import: " ++ modulePath

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
  if refName `M.member` stSubstMap st
    then pure (Right st)
    else do
      -- Check if this is an alias reference (alias::name)
      case break (== ':') refName of
        (aliasName, ':':':':actualName) | aliasName `M.member` stAliases st -> do
          -- Resolve alias reference
          let modulePath = stAliases st M.! aliasName
              qualifiedRef = modulePath ++ "::" ++ actualName
              newSubstMap = M.insert refName qualifiedRef (stSubstMap st)
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
              -- Check module import privacy only for top-level function names
              let modulePrefix = takeWhile (/= ':') fqn
              -- Block direct access ONLY if:
              -- 1. The module was imported via "import Module" (module import)
              -- 2. AND the refName exactly matches a top-level module name that should be accessed via qualified syntax
              -- 3. AND the refName doesn't match the module prefix (not a self-reference)
              if modulePrefix `S.member` stModuleImports st 
                 && '/' `notElem` refName  -- Only block simple names, allow compound names like "String/to_label/go"
                 && refName /= modulePrefix
                then do
                  -- This is a direct external call to a function from a module import - block it
                  loadRef st refName
                else do
                  -- Allow resolution - either auto-imported, internal call, or legitimate access
                  let newSubstMap = M.insert refName fqn (stSubstMap st)
                      newLoaded = S.insert refName (stLoaded st)
                  pure $ Right st { stSubstMap = newSubstMap, stLoaded = newLoaded }
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
    isSuffixOf :: Eq a => [a] -> [a] -> Bool
    isSuffixOf suffix str = suffix == drop (length str - length suffix) str

takeBaseName' :: FilePath -> String
takeBaseName' path = 
  if ".bend" `isSuffixOf'` path
     then take (length path - 5) path  -- Remove .bend extension but keep full path
     else path
  where
    isSuffixOf' :: Eq a => [a] -> [a] -> Bool
    isSuffixOf' suffix str = suffix == drop (length str - length suffix) str

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
            Right imported -> do
              let visited' = S.insert path (stVisited st)
                  merged   = mergeBooks (stBook st) imported
                  loaded'  = S.union (stLoaded st) (bookNames imported)
                  -- Auto-import should only work if refName matches the module name
                  importFilePrefix = takeBaseName' path ++ "::"
                  importQualified = importFilePrefix ++ refName
                  moduleName = takeBaseName' path
                  -- Add to substitution map ONLY if refName matches the module/file name
                  Book importedDefs _ = imported
                  newSubstMap = if refName == moduleName && importQualified `M.member` importedDefs
                              then M.insert refName importQualified (stSubstMap st)
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
generateImportPaths :: Name -> IO [FilePath]
generateImportPaths name = do
  isDir <- doesDirectoryExist name
  pure [ if isDir then name </> "_.bend" else name ++ ".bend" ]

hasSlash :: String -> Bool
hasSlash = any (== '/')

bookNames :: Book -> S.Set Name
bookNames (Book defs _) = S.fromList (M.keys defs)

mergeBooks :: Book -> Book -> Book
mergeBooks (Book defs1 names1) (Book defs2 names2) =
  Book (M.union defs1 defs2) (names1 ++ filter (`notElem` names1) names2)




