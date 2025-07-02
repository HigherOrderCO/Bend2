{-./Type.hs-}

module Core.Import (autoImport) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import System.Directory (doesFileExist, getCurrentDirectory)
import System.FilePath (takeDirectory, (</>))
import System.Exit (exitFailure)

import Core.Type
import Core.Deps
import Core.Parse.Book (doParseBook)

-- Auto-import unbound references in a Book
autoImport :: FilePath -> Book -> IO Book
autoImport _ book = do
  let deps = getBookDeps book
  result <- autoImportRefs book deps S.empty
  case result of
    Left err -> do
      putStrLn $ "Error: " ++ err
      exitFailure
    Right book' -> return book'

-- Collect all unbound references from a Book
-- collectUnboundRefs :: Book -> S.Set Name
-- collectUnboundRefs (Book defs) = S.unions $ map collectRefsFromDefn (M.elems defs) where
  -- collectRefsFromDefn (_, term, typ) = S.union (collectRefs term) (collectRefs typ)

-- Auto-import references with cycle detection
autoImportRefs :: Book -> S.Set Name -> S.Set FilePath -> IO (Either String Book)
autoImportRefs book refs _ | S.null refs = return (Right book)
autoImportRefs book refs visited = do
  result <- foldM (autoImportRef visited) (Right (book, S.empty)) (S.toList refs)
  case result of
    Left err -> return (Left err)
    Right (book', newRefs) ->
      if S.null newRefs
        then return (Right book')
        else autoImportRefs book' newRefs visited

-- Auto-import a single reference
-- FIXME: simplify this ugly code
autoImportRef :: S.Set FilePath -> Either String (Book, S.Set Name) -> Name -> IO (Either String (Book, S.Set Name))
autoImportRef _ (Left err) _ = return (Left err)
autoImportRef visited (Right (book@(Book defs), newRefs)) refName = do
  -- Check if the reference already exists in the book
  if M.member refName defs
    then return (Right (book, newRefs))
    else do
      let filePath = refName ++ ".bend"
      let pyFilePath = refName ++ ".bend.py"
      let altFilePath = refName </> "_.bend"
      let altPyFilePath = refName </> "_.bend.py"
      fileExists <- doesFileExist filePath
      pyFileExists <- doesFileExist pyFilePath
      altFileExists <- doesFileExist altFilePath
      altPyFileExists <- doesFileExist altPyFilePath
      -- Try the direct file first, then the Python file, then the alternative paths
      let (actualPath, pathExists) = if fileExists then (filePath, True)
                                      else if pyFileExists then (pyFilePath, True)
                                      else if altFileExists then (altFilePath, True)
                                      else if altPyFileExists then (altPyFilePath, True)
                                      else (filePath, False)
      if pathExists && not (actualPath `S.member` visited)
        then do
          content <- readFile actualPath
          case doParseBook actualPath content of
            Left err -> return (Left $ "Failed to parse " ++ actualPath ++ ": " ++ err)
            Right importedBook -> do
              -- Recursively auto-import the imported book
              let visited' = S.insert actualPath visited
              importResult <- autoImportRefs importedBook 
                                           (getBookDeps importedBook) visited'
              case importResult of
                Left err -> return (Left err)
                Right importedBook' -> do
                  -- Merge the imported book into the current book
                  let mergedBook = mergeBooks book importedBook'
                  let additionalRefs = getBookDeps importedBook'
                  return (Right (mergedBook, S.union newRefs additionalRefs))
        else
          return (Left $ "Definition '" ++ refName ++ "' not found. Expected file at: " ++ filePath ++ 
                        ", " ++ pyFilePath ++ ", " ++ altFilePath ++ " or " ++ altPyFilePath)

-- Merge two books, preferring definitions from the first book
mergeBooks :: Book -> Book -> Book
mergeBooks (Book defs1) (Book defs2) = Book (M.union defs1 defs2)
