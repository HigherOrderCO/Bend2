module Package.Resolve where

import Package.Types
import Package.Cache
import Package.HTTP
import Core.Parse.Parse (GitHubImport(..))
import Core.Parse.Book (doParseBook)
import qualified Core.Parse.Parse as Parse
import Core.Type (Book(..))

import Control.Monad (foldM, forM)
import Data.Either (partitionEithers)
import Data.List (intercalate, isSuffixOf)
import System.Directory (getDirectoryContents, doesFileExist)
import System.FilePath ((</>), takeExtension)
import qualified Data.Map.Strict as M
import qualified Data.Set as S

-- | Simple book merging function
mergeBooks :: Book -> Book -> Book
mergeBooks (Book defs1 names1) (Book defs2 names2) =
  Book (M.union defs1 defs2) (names1 ++ filter (`notElem` names1) names2)

-- | Result of resolving GitHub imports
data ResolveResult = ResolveResult
  { rrBook :: Book                     -- ^ Merged book from all resolved packages
  , rrPackageCache :: M.Map String FilePath -- ^ Package name to cache path mapping
  , rrErrors :: [String]               -- ^ Any errors encountered during resolution
  }

-- | Resolve a list of GitHub imports to cached packages
resolveGitHubImports :: [GitHubImport] -> IO ResolveResult
resolveGitHubImports ghImports = do
  config <- defaultCacheConfig
  resolveGitHubImportsWithConfig config ghImports

-- | Resolve GitHub imports with custom cache configuration
resolveGitHubImportsWithConfig :: CacheConfig -> [GitHubImport] -> IO ResolveResult
resolveGitHubImportsWithConfig config ghImports = do
  results <- forM ghImports (resolveGitHubImport config)
  
  let books = [book | Right (book, _, _) <- results]
      packageMappings = [mapping | Right (_, mapping, _) <- results]
      errors = [err | Left err <- results]
  
  let mergedBook = foldl mergeBooks (Book M.empty []) books
      mergedMappings = M.unions packageMappings
  
  return $ ResolveResult
    { rrBook = mergedBook
    , rrPackageCache = mergedMappings
    , rrErrors = errors
    }

-- | Resolve a single GitHub import
resolveGitHubImport :: CacheConfig -> GitHubImport -> IO (Either String (Book, M.Map String FilePath, [String]))
resolveGitHubImport config ghImport = do
  -- Convert GitHubImport to GitHubRepo
  let repo = GitHubRepo (Parse.ghOwner ghImport) (Parse.ghRepo ghImport) (Parse.ghRef ghImport)
  
  -- Download/cache the repository
  downloadResult <- downloadRepositoryWithCache repo config
  case downloadResult of
    Left err -> return $ Left $ "Failed to resolve " ++ formatGitHubImport ghImport ++ ": " ++ showPackageError err
    Right result -> do
      -- Parse the downloaded package to get a Book
      parseResult <- parsePackageAsBook result ghImport
      case parseResult of
        Left err -> return $ Left $ "Failed to parse " ++ formatGitHubImport ghImport ++ ": " ++ err
        Right book -> do
          -- Create package mapping
          let packageName = getPackageName ghImport
              packageMapping = M.singleton packageName (drFilePath result)
          return $ Right (book, packageMapping, [])

-- | Get the package name for an import (considering aliases)
getPackageName :: GitHubImport -> String
getPackageName ghImport =
  case Parse.ghAlias ghImport of
    Just alias -> alias
    Nothing -> Parse.ghRepo ghImport  -- Use repository name as default

-- | Format a GitHub import for error messages
formatGitHubImport :: GitHubImport -> String
formatGitHubImport ghImport = 
  let base = "gh:" ++ Parse.ghOwner ghImport ++ "/" ++ Parse.ghRepo ghImport
      withRef = case Parse.ghRef ghImport of
        Nothing -> base
        Just ref -> base ++ "@" ++ ref
      withSubpath = case Parse.ghSubpath ghImport of
        Nothing -> withRef
        Just subpath -> withRef ++ "/" ++ subpath
      withAlias = case Parse.ghAlias ghImport of
        Nothing -> withSubpath
        Just alias -> withSubpath ++ " as " ++ alias
  in withAlias

-- | Parse a downloaded package as a Bend Book
parsePackageAsBook :: DownloadResult -> GitHubImport -> IO (Either String Book)
parsePackageAsBook result ghImport = do
  -- Find all .bend files in the package directory
  bendFiles <- findBendFiles (drFilePath result)
  
  if null bendFiles
    then return $ Right $ Book M.empty []  -- No .bend files found
    else do
      -- Parse all files first WITHOUT prefixing to allow internal references
      parseResults <- mapM parseBendFileRaw bendFiles
      
      -- Check for parse errors  
      let (errors, books) = partitionEithers parseResults
      
      -- Merge all books first to create a complete internal context
      let internalBook = foldl mergeBooks (Book M.empty []) books
      
      -- Now apply package prefix to the merged result
      let packagePrefix = Parse.ghOwner ghImport ++ "/" ++ Parse.ghRepo ghImport
          finalBook = addPackagePrefix packagePrefix internalBook
      
      return $ Right finalBook
      
  where
    parseBendFileRaw :: FilePath -> IO (Either String Book)
    parseBendFileRaw filePath = do
      content <- readFile filePath
      case doParseBook filePath content of
        Left err -> return $ Left $ "Error in " ++ filePath ++ ": " ++ err
        Right book -> return $ Right book
    
    -- Add package prefix to all definitions in a book
    addPackagePrefix :: String -> Book -> Book
    addPackagePrefix prefix (Book defs names) =
      let prefixedDefs = M.mapKeys (addPrefix prefix) defs
          prefixedNames = map (addPrefix prefix) names
      in Book prefixedDefs prefixedNames
    
    addPrefix :: String -> String -> String
    addPrefix prefix name = prefix ++ "::" ++ name

-- | Find all .bend files recursively in a directory
findBendFiles :: FilePath -> IO [FilePath]
findBendFiles dir = do
  contents <- getDirectoryContents dir
  let realContents = filter (`notElem` [".", ".."]) contents
  files <- foldM collectBendFiles [] realContents
  return files
  where
    collectBendFiles :: [FilePath] -> FilePath -> IO [FilePath]
    collectBendFiles acc item = do
      let fullPath = dir </> item
      isFile <- doesFileExist fullPath
      if isFile
        then if ".bend" `isSuffixOf` item
             then return (fullPath : acc)
             else return acc
        else do
          -- It's a directory, recurse into it
          subFiles <- findBendFiles fullPath
          return (subFiles ++ acc)

-- | Show package error for user-friendly display
showPackageError :: PackageError -> String
showPackageError (NetworkError msg) = "Network error: " ++ msg
showPackageError (ParseError msg) = "Parse error: " ++ msg
showPackageError (NotFound msg) = "Not found: " ++ msg
showPackageError (RateLimited resetTime) = "Rate limited. Reset at: " ++ show resetTime
showPackageError (ExtractionError msg) = "Extraction error: " ++ msg
showPackageError (ValidationError msg) = "Validation error: " ++ msg

-- | Check for version conflicts between imports
checkVersionConflicts :: [GitHubImport] -> [String]
checkVersionConflicts ghImports = 
  let repoGroups = groupByRepo ghImports
      conflicts = filter hasConflict repoGroups
  in map formatConflict conflicts
  where
    groupByRepo :: [GitHubImport] -> [[(String, GitHubImport)]]
    groupByRepo imports = 
      let grouped = M.toList $ foldl groupImport M.empty imports
      in map snd grouped
      where
        groupImport acc ghImport = 
          let repoKey = Parse.ghOwner ghImport ++ "/" ++ Parse.ghRepo ghImport
              importInfo = (formatGitHubImport ghImport, ghImport)
          in M.insertWith (++) repoKey [importInfo] acc
    
    hasConflict :: [(String, GitHubImport)] -> Bool
    hasConflict imports = length (S.fromList $ map (Parse.ghRef . snd) imports) > 1
    
    formatConflict :: [(String, GitHubImport)] -> String
    formatConflict imports = 
      let repoName = Parse.ghOwner (snd $ head imports) ++ "/" ++ Parse.ghRepo (snd $ head imports)
          versions = map (show . Parse.ghRef . snd) imports
      in "Version conflict for repository " ++ repoName ++ ": " ++ intercalate ", " versions