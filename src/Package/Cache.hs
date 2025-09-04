{-# LANGUAGE OverloadedStrings #-}

module Package.Cache where

import Package.Types
import Package.Hash

import Control.Exception (try, SomeException)
import Control.Monad (when, unless, forM_)
import Data.Aeson (ToJSON(..), FromJSON(..), (.=), (.:))
import qualified Data.Aeson as JSON
import qualified Data.ByteString.Lazy as LBS
import Data.List (isPrefixOf)
import Data.Time (getCurrentTime, UTCTime)
import System.Directory
import System.FilePath
import System.IO (hPutStrLn, stderr)
import System.Posix.Files (readSymbolicLink)

-- | Configuration for cache management
data CacheConfig = CacheConfig
  { cacheRoot :: FilePath        -- ^ Root cache directory (default: ~/.bend/packages)
  , maxCacheSize :: Integer      -- ^ Maximum cache size in bytes (0 = unlimited)
  , maxAge :: Integer           -- ^ Maximum age in seconds (0 = unlimited)
  , autoCleanup :: Bool         -- ^ Automatically cleanup old packages
  } deriving (Show, Eq)

-- | Default cache configuration
defaultCacheConfig :: IO CacheConfig
defaultCacheConfig = do
  homeDir <- getHomeDirectory
  return $ CacheConfig
    { cacheRoot = homeDir </> ".bend" </> "packages"
    , maxCacheSize = 1024 * 1024 * 1024  -- 1GB default
    , maxAge = 30 * 24 * 60 * 60          -- 30 days
    , autoCleanup = True
    }

-- | Result of cache operations
data CacheResult
  = CacheHit FilePath          -- ^ Package found in cache
  | CacheMiss                  -- ^ Package not in cache
  | CacheError String          -- ^ Error accessing cache
  deriving (Show, Eq)

-- | Cache a downloaded package
cachePackage :: CacheConfig -> GitHubRepo -> String -> FilePath -> IO (Either PackageError FilePath)
cachePackage config repo commitSha sourcePath = do
  result <- try $ do
    -- Create cache directory structure
    let cacheDir = getCacheDir config repo commitSha
    createDirectoryIfMissing True cacheDir
    
    -- Copy package contents to cache
    copyDirectoryRecursive sourcePath cacheDir
    
    -- Create and save metadata
    metadata <- createPackageMetadata $ DownloadResult
      { drRepo = repo
      , drCommitHash = commitSha
      , drFilePath = cacheDir
      , drSize = 0  -- Will be calculated during metadata creation
      }
    
    let metadataPath = cacheDir </> ".bend-pkg-meta"
    LBS.writeFile metadataPath (JSON.encode metadata)
    
    -- Create index symlinks
    createCacheIndex config repo commitSha cacheDir
    
    return cacheDir
  
  case result of
    Left (ex :: SomeException) -> return $ Left $ ExtractionError $ "Cache error: " ++ show ex
    Right path -> return $ Right path

-- | Look up a package in the cache
lookupCached :: CacheConfig -> GitHubRepo -> Maybe String -> IO CacheResult
lookupCached config repo maybeRef = do
  cacheExists <- doesDirectoryExist (cacheRoot config)
  if not cacheExists
    then return CacheMiss
    else case maybeRef of
      Nothing -> lookupByIndex config repo "main"  -- Default to main branch
      Just ref -> do
        -- First try exact commit hash
        if length ref == 40 && all isHexChar ref
          then lookupByCommit config repo ref
          else lookupByIndex config repo ref
  where
    isHexChar c = (c >= '0' && c <= '9') || 
                  (c >= 'a' && c <= 'f') || 
                  (c >= 'A' && c <= 'F')

-- | Look up package by exact commit hash
lookupByCommit :: CacheConfig -> GitHubRepo -> String -> IO CacheResult
lookupByCommit config repo commitSha = do
  let cacheDir = getCacheDir config repo commitSha
  exists <- doesDirectoryExist cacheDir
  if exists
    then do
      -- Verify metadata exists and is valid
      let metadataPath = cacheDir </> ".bend-pkg-meta"
      metadataExists <- doesFileExist metadataPath
      if metadataExists
        then do
          -- TODO: Verify integrity
          return $ CacheHit cacheDir
        else return $ CacheError "Metadata file missing"
    else return CacheMiss

-- | Look up package by index (branch/tag name)
lookupByIndex :: CacheConfig -> GitHubRepo -> String -> IO CacheResult
lookupByIndex config repo ref = do
  let indexPath = getIndexPath config repo ref
  indexExists <- doesFileExist indexPath
  if indexExists
    then do
      target <- readSymbolicLink indexPath
      let fullPath = normalise $ takeDirectory indexPath </> target
      exists <- doesDirectoryExist fullPath
      if exists
        then return $ CacheHit fullPath
        else return $ CacheError "Index points to missing directory"
    else return CacheMiss

-- | Get the cache directory for a specific package version
getCacheDir :: CacheConfig -> GitHubRepo -> String -> FilePath
getCacheDir config repo commitSha =
  cacheRoot config </> "cache" </> "github.com" </> ghOwner repo </> ghName repo </> commitSha

-- | Get the index path for a package reference
getIndexPath :: CacheConfig -> GitHubRepo -> String -> FilePath
getIndexPath config repo ref =
  cacheRoot config </> "index" </> ("github.com-" ++ ghOwner repo ++ "-" ++ ghName repo ++ "-" ++ ref)

-- | Create index symlinks for quick lookup
createCacheIndex :: CacheConfig -> GitHubRepo -> String -> FilePath -> IO ()
createCacheIndex config repo commitSha cacheDir = do
  let indexDir = cacheRoot config </> "index"
  createDirectoryIfMissing True indexDir
  
  -- Create relative path from index to cache
  let relativePath = makeRelative indexDir cacheDir
  
  -- Create symlink for commit hash
  let commitIndexPath = getIndexPath config repo commitSha
  createSymbolicLinkIfMissing relativePath commitIndexPath
  
  -- If this is for a branch ref, we might want to update the branch index
  -- For now, we'll just create the commit-specific index
  
  where
    createSymbolicLinkIfMissing target linkPath = do
      exists <- doesFileExist linkPath
      unless exists $ do
        result <- try $ createFileLink target linkPath
        case result of
          Left (_ :: SomeException) -> 
            -- Fallback to copying if symbolic links aren't supported
            return ()
          Right _ -> return ()

-- | Copy directory recursively
copyDirectoryRecursive :: FilePath -> FilePath -> IO ()
copyDirectoryRecursive src dest = do
  createDirectoryIfMissing True dest
  contents <- listDirectory src
  forM_ contents $ \name -> do
    let srcPath = src </> name
    let destPath = dest </> name
    isDir <- doesDirectoryExist srcPath
    if isDir
      then copyDirectoryRecursive srcPath destPath
      else copyFile srcPath destPath

-- | Clean up old cache entries
cleanupCache :: CacheConfig -> IO ()
cleanupCache config = do
  exists <- doesDirectoryExist (cacheRoot config)
  when exists $ do
    -- Clean up by age if maxAge is set
    when (maxAge config > 0) $ cleanupByAge config
    
    -- Clean up by size if maxCacheSize is set
    when (maxCacheSize config > 0) $ cleanupBySize config
    
    -- Remove broken symlinks in index
    cleanupBrokenSymlinks config

-- | Remove packages older than maxAge
cleanupByAge :: CacheConfig -> IO ()
cleanupByAge config = do
  currentTime <- getCurrentTime
  let cacheDir = cacheRoot config </> "cache" </> "github.com"
  exists <- doesDirectoryExist cacheDir
  when exists $ do
    -- TODO: Implement age-based cleanup
    -- This would iterate through all cached packages and remove old ones
    return ()

-- | Remove oldest packages to stay under maxCacheSize
cleanupBySize :: CacheConfig -> IO ()
cleanupBySize config = do
  -- TODO: Implement size-based cleanup
  -- This would calculate total cache size and remove oldest packages
  return ()

-- | Remove broken symlinks from index
cleanupBrokenSymlinks :: CacheConfig -> IO ()
cleanupBrokenSymlinks config = do
  let indexDir = cacheRoot config </> "index"
  exists <- doesDirectoryExist indexDir
  when exists $ do
    indexFiles <- listDirectory indexDir
    forM_ indexFiles $ \indexFile -> do
      let indexPath = indexDir </> indexFile
      isSymLink <- pathIsSymbolicLink indexPath
      when isSymLink $ do
        target <- try $ readSymbolicLink indexPath
        case target of
          Left (_ :: SomeException) -> removeFile indexPath
          Right targetPath -> do
            let fullTargetPath = normalise $ indexDir </> targetPath
            targetExists <- doesDirectoryExist fullTargetPath
            unless targetExists $ removeFile indexPath

-- | Validate cache integrity
validateCache :: CacheConfig -> IO [String]
validateCache config = do
  -- TODO: Implement cache validation
  -- This would check all cached packages for:
  -- - Missing metadata files
  -- - Corrupted content hashes
  -- - Broken directory structures
  return []

-- JSON instances for PackageMetadata
instance ToJSON PackageMetadata where
  toJSON pm = JSON.object
    [ "source" .= JSON.object
        [ "type" .= ("github" :: String)
        , "owner" .= ghOwner (pmSource pm)
        , "repo" .= ghName (pmSource pm)
        , "ref" .= ghRef (pmSource pm)
        ]
    , "commit" .= pmCommit pm
    , "downloaded" .= pmDownloaded pm
    , "content_hash" .= pmContentHash pm
    , "bend_files" .= pmBendFiles pm
    ]

instance FromJSON PackageMetadata where
  parseJSON = JSON.withObject "PackageMetadata" $ \o -> do
    source <- o .: "source"
    sourceType <- source .: "type"
    if sourceType /= ("github" :: String)
      then fail "Only GitHub sources supported"
      else do
        owner <- source .: "owner"
        repo <- source .: "repo"
        ref <- source .: "ref"
        commit <- o .: "commit"
        downloaded <- o .: "downloaded"
        contentHash <- o .: "content_hash"
        bendFiles <- o .: "bend_files"
        return $ PackageMetadata
          { pmSource = GitHubRepo owner repo ref
          , pmCommit = commit
          , pmDownloaded = downloaded
          , pmContentHash = contentHash
          , pmBendFiles = bendFiles
          }