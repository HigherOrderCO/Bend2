{-./Type.hs-}

module Core.Import (autoImport) where

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
import Core.Subst (substituteRefs, SubstMap, substituteRefsInBook)
import qualified Data.Map.Strict as M

-- Public API

autoImport :: FilePath -> Book -> IO Book
autoImport root book = do
  result <- importAll root book
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
  }

importAll :: FilePath -> Book -> IO (Either String Book)
importAll currentFile base = do
  let initial = ImportState
        { stVisited = S.empty
        , stLoaded  = bookNames base
        , stBook    = base
        , stSubstMap = M.empty
        , stCurrentFile = currentFile
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
            Right st'  ->
              -- Recompute deps on the combined book, keep processing
              let deps' = getBookDeps (stBook st')
                  next  = S.union rest deps'
              in importLoop st' next

-- | Resolve a reference by building substitution map entry
resolveRef :: ImportState -> Name -> IO (Either String ImportState)
resolveRef st refName = do
  -- First check if it's already in the substitution map
  if refName `M.member` stSubstMap st
    then pure (Right st)
    else do
      -- Check if it's a local reference (qualified version exists in current book)
      let currentFilePrefix = takeBaseName (stCurrentFile st) ++ "::"
          localQualified = currentFilePrefix ++ refName
          Book defs _ = stBook st
      
      if localQualified `M.member` defs
        then do
          -- It's a local reference - add to substitution map
          let newSubstMap = M.insert refName localQualified (stSubstMap st)
              newLoaded = S.insert refName (stLoaded st)
          pure $ Right st { stSubstMap = newSubstMap, stLoaded = newLoaded }
        else do
          -- It's not local - try auto-import
          loadRef st refName
  where
    takeBaseName :: FilePath -> String
    takeBaseName path = 
      let name = reverse . takeWhile (/= '/') . reverse $ path
      in if ".bend" `isSuffixOf` name
         then take (length name - 5) name
         else name
    isSuffixOf :: Eq a => [a] -> [a] -> Bool
    isSuffixOf suffix str = suffix == drop (length str - length suffix) str

takeBaseName' :: FilePath -> String
takeBaseName' path = 
  let name = reverse . takeWhile (/= '/') . reverse $ path
  in if ".bend" `isSuffixOf'` name
     then take (length name - 5) name
     else name
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
                  -- Find the qualified name for the reference in the imported module
                  importFilePrefix = takeBaseName' path ++ "::"
                  importQualified = importFilePrefix ++ refName
                  -- Add to substitution map if the qualified name exists in imported book
                  Book importedDefs _ = imported
                  newSubstMap = if importQualified `M.member` importedDefs
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




