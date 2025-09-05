{-# LANGUAGE OverloadedStrings #-}

module Package.Install where

import Package.Types
import Package.Cache
import Package.HTTP
import Package.Hash (createPackageMetadata)
import Package.Resolve (showPackageError)
import qualified Core.Parse.Parse as Parse

import Control.Exception (try, SomeException, bracket)
import Control.Monad (forM, forM_, when, unless)
import Data.Aeson (ToJSON(..), FromJSON(..), (.=), (.:))
import qualified Data.Aeson as JSON
import qualified Data.ByteString.Lazy as LBS
import Data.List (nub)
import Data.Time (getCurrentTime, UTCTime)
import System.Directory
import System.FilePath
import System.IO (hPutStrLn, stderr)
import qualified Data.Map.Strict as M
import qualified Data.Set as S

-- | Configuration for local package installation
data InstallConfig = InstallConfig
  { projectRoot :: FilePath       -- ^ Root directory of the project
  , packagesDir :: FilePath       -- ^ Local packages directory (default: ./bend_packages)
  , forceReinstall :: Bool        -- ^ Force reinstallation even if package exists
  } deriving (Show, Eq)

-- | Default installation configuration
defaultInstallConfig :: IO InstallConfig
defaultInstallConfig = do
  cwd <- getCurrentDirectory
  return $ InstallConfig
    { projectRoot = cwd
    , packagesDir = cwd </> "bend_packages"
    , forceReinstall = False
    }

-- | Package lock file to track installed versions
data PackageLock = PackageLock
  { lockPackages :: M.Map String PackageLockEntry
  , lockGenerated :: UTCTime
  } deriving (Show, Eq)

data PackageLockEntry = PackageLockEntry
  { pleOwner :: String
  , pleRepo :: String
  , pleRef :: Maybe String
  , pleCommit :: String
  , pleInstallPath :: FilePath
  , pleContentHash :: String
  } deriving (Show, Eq)

instance ToJSON PackageLock where
  toJSON lock = JSON.object
    [ "packages" .= lockPackages lock
    , "generated" .= lockGenerated lock
    ]

instance FromJSON PackageLock where
  parseJSON = JSON.withObject "PackageLock" $ \o -> do
    packages <- o .: "packages"
    generated <- o .: "generated"
    return $ PackageLock packages generated

instance ToJSON PackageLockEntry where
  toJSON entry = JSON.object
    [ "owner" .= pleOwner entry
    , "repo" .= pleRepo entry
    , "ref" .= pleRef entry
    , "commit" .= pleCommit entry
    , "path" .= pleInstallPath entry
    , "hash" .= pleContentHash entry
    ]

instance FromJSON PackageLockEntry where
  parseJSON = JSON.withObject "PackageLockEntry" $ \o -> do
    owner <- o .: "owner"
    repo <- o .: "repo"
    ref <- o .: "ref"
    commit <- o .: "commit"
    path <- o .: "path"
    hash <- o .: "hash"
    return $ PackageLockEntry owner repo ref commit path hash

-- | Install packages from GitHub imports to local bend_packages directory
installPackages :: InstallConfig -> [Parse.GitHubImport] -> IO (Either String PackageLock)
installPackages config ghImports = do
  -- Create bend_packages directory if it doesn't exist
  createDirectoryIfMissing True (packagesDir config)
  
  -- Load existing lock file if present
  existingLock <- loadPackageLock config
  
  -- Process each GitHub import
  results <- mapM (installPackage config existingLock) ghImports
  
  -- Check for errors
  let errors = [err | Left err <- results]
  if not (null errors)
    then return $ Left $ unlines errors
    else do
      -- Create new lock file
      let entries = [entry | Right entry <- results]
          lockMap = M.fromList [(getPackageName' entry, entry) | entry <- entries]
      now <- getCurrentTime
      let newLock = PackageLock lockMap now
      
      -- Save lock file
      saveLockFile <- savePackageLock config newLock
      case saveLockFile of
        Left err -> return $ Left err
        Right () -> return $ Right newLock

-- | Install a single package
installPackage :: InstallConfig -> Maybe PackageLock -> Parse.GitHubImport -> IO (Either String PackageLockEntry)
installPackage config maybeLock ghImport = do
  let packageName = case Parse.ghAlias ghImport of
        Just alias -> alias
        Nothing -> Parse.ghRepo ghImport
      targetDir = packagesDir config </> packageName
  
  -- Check if package already exists
  exists <- doesDirectoryExist targetDir
  
  -- Check lock file for existing installation
  let shouldInstall = case maybeLock of
        Nothing -> True
        Just lock -> case M.lookup packageName (lockPackages lock) of
          Nothing -> True
          Just entry -> 
            -- Check if the requested version matches
            forceReinstall config ||
            pleOwner entry /= Parse.ghOwner ghImport ||
            pleRepo entry /= Parse.ghRepo ghImport ||
            pleRef entry /= Parse.ghRef ghImport
  
  if exists && not shouldInstall
    then do
      -- Package already installed and up to date
      case maybeLock >>= \lock -> M.lookup packageName (lockPackages lock) of
        Just entry -> return $ Right entry
        Nothing -> return $ Left $ "Package " ++ packageName ++ " exists but not in lock file"
    else do
      -- Need to install/reinstall the package
      when exists $ do
        -- Remove existing package directory
        removeDirectoryRecursive targetDir
      
      -- Download the package using existing infrastructure
      cacheConfig <- defaultCacheConfig
      let repo = GitHubRepo (Parse.ghOwner ghImport) (Parse.ghRepo ghImport) (Parse.ghRef ghImport)
      downloadResult <- downloadRepositoryWithCache repo cacheConfig
      
      case downloadResult of
        Left err -> return $ Left $ "Failed to download " ++ packageName ++ ": " ++ showPackageError err
        Right result -> do
          -- Copy from cache to local bend_packages
          copyResult <- try $ copyDirectoryRecursiveLocal (drFilePath result) targetDir
          case copyResult of
            Left (e :: SomeException) -> return $ Left $ "Failed to copy package: " ++ show e
            Right () -> do
              -- Create lock entry
              metadata <- createPackageMetadata result
              let entry = PackageLockEntry
                    { pleOwner = Parse.ghOwner ghImport
                    , pleRepo = Parse.ghRepo ghImport
                    , pleRef = Parse.ghRef ghImport
                    , pleCommit = drCommitHash result
                    , pleInstallPath = targetDir
                    , pleContentHash = pmContentHash metadata
                    }
              return $ Right entry

-- | Get package name from lock entry
getPackageName' :: PackageLockEntry -> String
getPackageName' entry = pleRepo entry

-- | Load package lock file
loadPackageLock :: InstallConfig -> IO (Maybe PackageLock)
loadPackageLock config = do
  let lockPath = projectRoot config </> ".bend-pkg-lock"
  exists <- doesFileExist lockPath
  if not exists
    then return Nothing
    else do
      content <- LBS.readFile lockPath
      case JSON.decode content of
        Nothing -> return Nothing
        Just lock -> return $ Just lock

-- | Save package lock file
savePackageLock :: InstallConfig -> PackageLock -> IO (Either String ())
savePackageLock config lock = do
  result <- try $ do
    let lockPath = projectRoot config </> ".bend-pkg-lock"
    LBS.writeFile lockPath (encodePretty lock)
  case result of
    Left (e :: SomeException) -> return $ Left $ "Failed to save lock file: " ++ show e
    Right () -> return $ Right ()
  where
    -- Pretty encoding with indentation (just use encode for now)
    encodePretty = JSON.encode

-- | Copy directory recursively (local version to avoid name conflict)
copyDirectoryRecursiveLocal :: FilePath -> FilePath -> IO ()
copyDirectoryRecursiveLocal src dst = do
  createDirectoryIfMissing True dst
  contents <- listDirectory src
  forM_ contents $ \item -> do
    let srcPath = src </> item
        dstPath = dst </> item
    isDir <- doesDirectoryExist srcPath
    if isDir
      then copyDirectoryRecursiveLocal srcPath dstPath
      else copyFile srcPath dstPath

-- | Clean bend_packages directory
cleanPackages :: InstallConfig -> IO ()
cleanPackages config = do
  let dir = packagesDir config
  exists <- doesDirectoryExist dir
  when exists $ removeDirectoryRecursive dir

-- | Check if all packages in lock file are installed
verifyPackages :: InstallConfig -> IO [(String, Bool)]
verifyPackages config = do
  maybeLock <- loadPackageLock config
  case maybeLock of
    Nothing -> return []
    Just lock -> do
      let entries = M.toList (lockPackages lock)
      forM entries $ \(name, entry) -> do
        exists <- doesDirectoryExist (pleInstallPath entry)
        return (name, exists)

-- | List installed packages
listInstalledPackages :: InstallConfig -> IO [(String, PackageLockEntry)]
listInstalledPackages config = do
  maybeLock <- loadPackageLock config
  case maybeLock of
    Nothing -> return []
    Just lock -> return $ M.toList (lockPackages lock)