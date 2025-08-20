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

-- Public API

autoImport :: FilePath -> Book -> IO Book
autoImport _root book = do
  result <- importAll book
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
  }

importAll :: Book -> IO (Either String Book)
importAll base = do
  let initial = ImportState
        { stVisited = S.empty
        , stLoaded  = bookNames base
        , stBook    = base
        }
      pending0 = getBookDeps base
  res <- importLoop initial pending0
  pure $ fmap stBook res

importLoop :: ImportState -> S.Set Name -> IO (Either String ImportState)
importLoop st pending =
  case S.minView pending of
    Nothing -> pure (Right st)
    Just (ref, rest)
      | ref `S.member` stLoaded st -> importLoop st rest
      | otherwise -> do
          r <- loadRef st ref
          case r of
            Left err   -> pure (Left err)
            Right st'  ->
              -- Recompute deps on the combined book, keep processing
              let deps' = getBookDeps (stBook st')
                  next  = S.union rest deps'
              in importLoop st' next

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
              pure $ Right st { stVisited = visited', stLoaded = loaded', stBook = merged }
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



