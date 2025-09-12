{-# LANGUAGE OverloadedStrings #-}

module Package.Index where

import Control.Exception (try, SomeException)
import Control.Monad (forM)
import Data.Aeson (ToJSON(..), FromJSON(..), (.=), (.:), (.:?))
import qualified Data.Aeson as JSON
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Map.Strict as M
import qualified Data.Aeson.KeyMap as KM
import Data.List (intercalate)
import Network.HTTP.Simple
import System.Directory (createDirectoryIfMissing, doesFileExist)
import System.FilePath ((</>), takeDirectory)
import System.IO (hPutStrLn, stderr)

-- | Package index API configuration
data IndexConfig = IndexConfig
  { apiBaseUrl :: String      -- ^ Base URL of the package index API
  , cacheDir :: FilePath      -- ^ Local cache directory (bend_packages)
  } deriving (Show, Eq)

-- | Default configuration pointing to localhost for testing
defaultIndexConfig :: IO IndexConfig
defaultIndexConfig = do
  return $ IndexConfig
    { apiBaseUrl = "http://localhost:3000"
    , cacheDir = "bend_packages"
    }

-- | Package index import specification
data PackageIndexImport = PackageIndexImport
  { piOwner :: String           -- ^ Package owner (e.g., "VictorTaelin")
  , piPackage :: String         -- ^ Package name (e.g., "VecAlg") 
  , piPath :: String            -- ^ Path to definition (e.g., "List/dot")
  , piVersion :: Maybe String   -- ^ Version (Nothing = latest)
  , piAlias :: Maybe String     -- ^ Optional import alias
  } deriving (Show, Eq)

-- | Response from the package index resolve API
data ResolveResponse = ResolveResponse
  { rrFile :: String                      -- ^ File path like "owner/package#version/path"
  , rrContent :: String                   -- ^ Source code content
  , rrDependencies :: [ResolveResponse]   -- ^ Nested dependencies
  } deriving (Show, Eq)

instance FromJSON ResolveResponse where
  parseJSON = JSON.withObject "ResolveResponse" $ \o -> do
    file <- o .: "file"
    content <- o .: "content" 
    deps <- o .:? "dependencies" JSON..!= []
    return $ ResolveResponse file content deps

-- | Resolve a definition and all its dependencies from the package index
resolveDefinition :: IndexConfig -> PackageIndexImport -> IO (Either String ResolveResponse)
resolveDefinition config pkgImport = do
  let url = buildResolveUrl config pkgImport
  result <- try $ do
    request <- parseRequest ("GET " ++ url)
    response <- httpLBS request
    let statusCode = getResponseStatusCode response
    if statusCode == 200
      then do
        let body = getResponseBody response
        case JSON.decode body of
          Nothing -> return $ Left "Failed to decode API response"
          Just resolveResp -> return $ Right resolveResp
      else do
        let body = getResponseBody response
        let errorMsg = case JSON.decode body of
              Just (JSON.Object obj) -> case KM.lookup "error" obj of
                Just (JSON.String err) -> show err
                _ -> "HTTP " ++ show statusCode
              _ -> "HTTP " ++ show statusCode ++ ": " ++ show body
        return $ Left errorMsg
  
  case result of
    Left (e :: SomeException) -> return $ Left $ "Network error: " ++ show e
    Right res -> return res

-- | Build the resolve API URL
buildResolveUrl :: IndexConfig -> PackageIndexImport -> String
buildResolveUrl config pkgImport = 
  let version = case piVersion pkgImport of
        Nothing -> "latest"
        Just v -> v
      path = piPath pkgImport
  in apiBaseUrl config ++ "/api/definitions/resolve/" 
     ++ piOwner pkgImport ++ "/" 
     ++ piPackage pkgImport ++ "/" 
     ++ path ++ "/" 
     ++ version

-- | Install resolved definitions to local bend_packages directory
installResolvedDefinitions :: IndexConfig -> ResolveResponse -> IO (Either String ())
installResolvedDefinitions config resolved = do
  result <- try $ installDefinition resolved
  case result of
    Left (e :: SomeException) -> return $ Left $ "Installation error: " ++ show e
    Right () -> return $ Right ()
  where
    installDefinition :: ResolveResponse -> IO ()
    installDefinition resp = do
      -- Convert file path to local file path
      let localPath = cacheDir config </> rrFile resp ++ ".bend"
      
      -- Create directory if needed
      createDirectoryIfMissing True (takeDirectory localPath)
      
      -- Write the file content
      writeFile localPath (rrContent resp)
      
      -- Recursively install dependencies
      mapM_ installDefinition (rrDependencies resp)

-- | Parse package index import from import string
-- Examples:
--   "VictorTaelin/VecAlg/List/dot" -> PackageIndexImport "VictorTaelin" "VecAlg" "List/dot" Nothing
--   "VictorTaelin/VecAlg#7/List/dot" -> PackageIndexImport "VictorTaelin" "VecAlg" "List/dot" (Just "7")
parsePackageIndexImport :: String -> Maybe String -> Maybe PackageIndexImport
parsePackageIndexImport importStr alias = do
  case break (== '/') importStr of
    (owner, '/':rest1) -> do
      case break (== '/') rest1 of
        (packageWithVersion, '/':path) -> do
          let (package, version) = parseVersion packageWithVersion
          return $ PackageIndexImport owner package path version alias
        _ -> Nothing
    _ -> Nothing
  where
    parseVersion :: String -> (String, Maybe String)
    parseVersion str = 
      case break (== '#') str of
        (pkg, '#':ver) -> (pkg, Just ver)
        (pkg, "") -> (pkg, Nothing)
        _ -> (str, Nothing)

-- | Import a definition using the package index
importDefinition :: IndexConfig -> String -> Maybe String -> IO (Either String ResolveResponse)
importDefinition config importStr alias = do
  case parsePackageIndexImport importStr alias of
    Nothing -> return $ Left $ "Invalid import format: " ++ importStr
    Just pkgImport -> do
      result <- resolveDefinition config pkgImport
      case result of
        Left err -> return $ Left err
        Right resolved -> do
          installResult <- installResolvedDefinitions config resolved
          case installResult of
            Left installErr -> return $ Left installErr
            Right () -> return $ Right resolved

-- | Check if a definition is already cached locally
isCached :: IndexConfig -> PackageIndexImport -> IO Bool
isCached config pkgImport = do
  let localPath = cacheDir config </> 
        piOwner pkgImport ++ "/" ++ 
        piPackage pkgImport ++ 
        (case piVersion pkgImport of
          Nothing -> ""
          Just v -> "#" ++ v) ++ "/" ++
        piPath pkgImport ++ ".bend"
  doesFileExist localPath