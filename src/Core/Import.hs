{-./Type.hs-}

module Core.Import (autoImport) where

import Control.Monad (foldM)
import Data.List (intercalate)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import System.Directory (doesFileExist, getCurrentDirectory)
import System.FilePath (takeDirectory, (</>))
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import Core.Type
import Core.Deps
import Core.Parse.Book (doParseBook)

-- Auto-import unbound references in a Book
autoImport :: FilePath -> Book -> IO Book
autoImport _ book = do
  let deps = getBookDeps book
  result <- importDependencies book deps S.empty
  case result of
    Left err -> do
      hPutStrLn stderr $ "Error: " ++ err
      exitFailure
    Right book' -> return book'

-- Import dependencies with cycle detection
importDependencies :: Book -> S.Set Name -> S.Set FilePath -> IO (Either String Book)
importDependencies book refs visited
  | S.null refs = return (Right book)
  | otherwise = do
      result <- foldM (importSingleDep visited) (Right (book, S.empty)) (S.toList refs)
      case result of
        Left err -> return (Left err)
        Right (book', newRefs) ->
          if S.null newRefs
            then return (Right book')
            else importDependencies book' newRefs visited

-- Import a single dependency
importSingleDep :: S.Set FilePath -> Either String (Book, S.Set Name) -> Name -> IO (Either String (Book, S.Set Name))
importSingleDep _ (Left err) _ = return (Left err)
importSingleDep visited (Right (book@(Book defs _), newRefs)) refName
  | M.member refName defs = return (Right (book, newRefs))
  | otherwise = do
      maybeResult <- tryImportPaths refName visited
      case maybeResult of
        Nothing -> handleMissingImport refName book newRefs
        Just (path, content) -> processImportedFile path content visited book newRefs

-- Try different file paths for import
tryImportPaths :: Name -> S.Set FilePath -> IO (Maybe (FilePath, String))
tryImportPaths refName visited = do
  let paths = generateImportPaths refName
  tryPaths paths visited
  where
    tryPaths [] _ = return Nothing
    tryPaths (path:rest) vis
      | path `S.member` vis = tryPaths rest vis
      | otherwise = do
          exists <- doesFileExist path
          if exists
            then Just . (path,) <$> readFile path
            else tryPaths rest vis

-- Generate possible import paths
generateImportPaths :: Name -> [FilePath]
generateImportPaths name =
  [ name ++ ".bend"
  , name </> "_.bend"
  ]

-- Process an imported file
processImportedFile :: FilePath -> String -> S.Set FilePath -> Book -> S.Set Name -> IO (Either String (Book, S.Set Name))
processImportedFile path content visited book newRefs = do
  case doParseBook path content of
    Left err -> return $ Left $ "Failed to parse " ++ path ++ ": " ++ err
    Right importedBook -> do
      let visited' = S.insert path visited
      importResult <- importDependencies importedBook (getBookDeps importedBook) visited'
      case importResult of
        Left err -> return (Left err)
        Right importedBook' -> do
          let mergedBook = mergeBooks book importedBook'
          let additionalRefs = getBookDeps importedBook'
          return (Right (mergedBook, S.union newRefs additionalRefs))

-- Handle missing imports
handleMissingImport :: Name -> Book -> S.Set Name -> IO (Either String (Book, S.Set Name))
handleMissingImport refName book newRefs
  | '/' `elem` refName = do
      let paths = generateImportPaths refName
      return $ Left $
        "Import error: Could not find file for '" ++ refName ++ "'. " ++
        "Tried: " ++ intercalate ", " paths
  | otherwise = return $ Right (book, newRefs)

-- Merge two books, preferring definitions from the first book
mergeBooks :: Book -> Book -> Book
mergeBooks (Book defs1 names1) (Book defs2 names2) = 
  Book (M.union defs1 defs2) (names1 ++ filter (`notElem` names1) names2)
