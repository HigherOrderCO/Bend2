module Package.Index
  ( IndexConfig(..)
  , defaultIndexConfig
  , ensureFile
  ) where

import Control.Exception (SomeException, try)
import qualified Data.ByteString.Lazy as LBS
import Network.HTTP.Simple
import System.Directory (createDirectoryIfMissing, doesFileExist)
import System.FilePath ((</>), takeDirectory)
import qualified System.FilePath as FP
import Data.List.Split (splitOn)

-- | Package index configuration
data IndexConfig = IndexConfig
  { apiBaseUrl  :: String      -- ^ Base URL for the package index
  , bendRootDir :: FilePath    -- ^ Local BendRoot directory
  } deriving (Show, Eq)

-- | Default configuration using localhost for the package server
defaultIndexConfig :: FilePath -> IO IndexConfig
defaultIndexConfig root =
  pure $ IndexConfig
    { apiBaseUrl = "http://localhost:3000"
    , bendRootDir = root
    }

-- | Ensure a file exists locally, downloading it from the package server if needed.
--   The path must be expressed using POSIX separators relative to BendRoot.
ensureFile :: IndexConfig -> FilePath -> IO (Either String ())
ensureFile config posixPath = do
  let systemPath = fromPosixPath posixPath
      localPath = bendRootDir config </> systemPath
  exists <- doesFileExist localPath
  if exists
    then pure (Right ())
    else downloadFile localPath
  where
    downloadFile localPath = do
      let encodedPath = encodePath posixPath
          url = apiBaseUrl config ++ "/api/files/" ++ encodedPath
      putStrLn $ "[package-index] GET " ++ url
      result <- try $ do
        request <- parseRequest ("GET " ++ url)
        response <- httpLBS request
        let status = getResponseStatusCode response
        if status == 200
          then do
            createDirectoryIfMissing True (takeDirectory localPath)
            LBS.writeFile localPath (getResponseBody response)
            pure (Right ())
          else pure (Left ("HTTP " ++ show status))
      case result of
        Left (e :: SomeException) -> pure (Left ("Network error: " ++ show e))
        Right res -> pure res

    fromPosixPath :: FilePath -> FilePath
    fromPosixPath = FP.joinPath . splitOn "/"

    encodePath :: FilePath -> String
    encodePath = concatMap encodeChar

    encodeChar :: Char -> String
    encodeChar '#' = "%23"
    encodeChar ' ' = "%20"
    encodeChar c   = [c]
