{-# LANGUAGE OverloadedStrings #-}

module Package.HTTP where

import Package.Types

import Control.Exception (try, SomeException)
import Data.Aeson ((.:), (.:?))
import qualified Data.Aeson as JSON
import qualified Data.Aeson.Types as JSON
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Vector as V
import Network.HTTP.Simple
import Network.HTTP.Conduit (HttpException)
import System.Directory
import System.FilePath
import System.IO.Temp (withSystemTempDirectory, createTempDirectory, getCanonicalTemporaryDirectory)
import qualified Codec.Archive.Zip as Zip

-- | Download a GitHub repository and extract it
downloadRepository :: GitHubRepo -> IO (Either PackageError DownloadResult)
downloadRepository repo = do
  -- First, resolve the ref to a commit SHA if needed
  commitResult <- resolveRef repo
  case commitResult of
    Left err -> return $ Left err
    Right commitSha -> do
      -- Download the archive
      archiveResult <- downloadArchive repo commitSha
      case archiveResult of
        Left err -> return $ Left err
        Right (archiveData, size) -> do
          -- Extract to temp directory (don't auto-delete for debugging)
          tmpDir <- getCanonicalTemporaryDirectory >>= \tmp -> 
            createTempDirectory tmp "bend-pkg-"
          extractResult <- extractArchive archiveData tmpDir
          case extractResult of
            Left err -> return $ Left err
            Right extractedPath -> do
              return $ Right $ DownloadResult
                { drRepo = repo
                , drCommitHash = commitSha
                , drFilePath = extractedPath
                , drSize = size
                }

-- | Resolve a ref (branch/tag) to a commit SHA
-- If no ref is provided, uses the default branch
resolveRef :: GitHubRepo -> IO (Either PackageError String)
resolveRef repo = do
  case ghRef repo of
    Nothing -> do
      -- Get default branch
      repoInfoResult <- getRepoInfo repo
      case repoInfoResult of
        Left err -> return $ Left err
        Right info -> do
          -- Get commit SHA for default branch
          getCommitSha repo (riDefaultBranch info)
    Just ref -> do
      -- Check if ref is already a SHA (40 hex chars)
      if length ref == 40 && all isHexChar ref
        then return $ Right ref
        else getCommitSha repo ref
  where
    isHexChar c = (c >= '0' && c <= '9') || 
                  (c >= 'a' && c <= 'f') || 
                  (c >= 'A' && c <= 'F')

-- | Get repository information from GitHub API
getRepoInfo :: GitHubRepo -> IO (Either PackageError RepoInfo)
getRepoInfo repo = do
  let url = "https://api.github.com/repos/" ++ ghOwner repo ++ "/" ++ ghName repo
  request <- parseRequest url
  let requestWithHeaders = setRequestHeaders 
        [ ("User-Agent", "bend-package-manager")
        , ("Accept", "application/vnd.github.v3+json")
        ] request
  
  result <- try $ httpJSON requestWithHeaders :: IO (Either HttpException (Response JSON.Value))
  case result of
    Left ex -> return $ Left $ NetworkError $ show ex
    Right response -> do
      let status = getResponseStatusCode response
      if status == 200
        then do
          let body = getResponseBody response
          case JSON.fromJSON body of
            JSON.Success info -> return $ Right info
            JSON.Error err -> return $ Left $ ParseError $ "Failed to parse repo info: " ++ err
        else if status == 404
          then return $ Left $ NotFound $ "Repository not found: " ++ ghOwner repo ++ "/" ++ ghName repo
        else if status == 403
          then do
            let headers = getResponseHeaders response
            case lookup "X-RateLimit-Reset" headers of
              Just resetTime -> return $ Left $ RateLimited $ read $ T.unpack $ TE.decodeUtf8 resetTime
              Nothing -> return $ Left $ NetworkError $ "Rate limited (status 403)"
          else return $ Left $ NetworkError $ "GitHub API error: " ++ show status

-- | Get commit SHA for a ref (branch/tag name)
getCommitSha :: GitHubRepo -> String -> IO (Either PackageError String)
getCommitSha repo ref = do
  -- Try as branch first
  let branchUrl = "https://api.github.com/repos/" ++ ghOwner repo ++ "/" ++ ghName repo ++ "/branches/" ++ ref
  request <- parseRequest branchUrl
  let requestWithHeaders = setRequestHeaders
        [ ("User-Agent", "bend-package-manager")
        , ("Accept", "application/vnd.github.v3+json")
        ] request
  
  result <- try $ httpJSON requestWithHeaders :: IO (Either HttpException (Response JSON.Value))
  case result of
    Left _ -> tryAsTag  -- If branch fails, try as tag
    Right response -> do
      let status = getResponseStatusCode response
      if status == 200
        then do
          let body = getResponseBody response
          case body of
            JSON.Object obj -> do
              case JSON.fromJSON (JSON.Object obj) :: JSON.Result CommitRef of
                JSON.Success commitRef -> return $ Right $ crSha commitRef
                JSON.Error err -> return $ Left $ ParseError $ "Failed to parse branch info: " ++ err
            _ -> return $ Left $ ParseError "Unexpected response format"
        else tryAsTag
  where
    tryAsTag = do
      let tagUrl = "https://api.github.com/repos/" ++ ghOwner repo ++ "/" ++ ghName repo ++ "/tags"
      request <- parseRequest tagUrl
      let requestWithHeaders = setRequestHeaders
            [ ("User-Agent", "bend-package-manager")
            , ("Accept", "application/vnd.github.v3+json")
            ] request
      
      result <- try $ httpJSON requestWithHeaders :: IO (Either HttpException (Response JSON.Value))
      case result of
        Left ex -> return $ Left $ NetworkError $ show ex
        Right response -> do
          let status = getResponseStatusCode response
          if status == 200
            then do
              let body = getResponseBody response
              case body of
                JSON.Array tags -> do
                  -- Look for matching tag
                  let matchingTag = findTag ref tags
                  case matchingTag of
                    Just sha -> return $ Right sha
                    Nothing -> return $ Left $ NotFound $ "Ref not found: " ++ ref
                _ -> return $ Left $ ParseError "Unexpected tags format"
            else return $ Left $ NotFound $ "Ref not found: " ++ ref
    
    findTag :: String -> V.Vector JSON.Value -> Maybe String
    findTag targetRef arr = 
      let tags = V.toList arr
      in case filter (matchesTag targetRef) tags of
           (JSON.Object obj : _) -> 
             case JSON.fromJSON (JSON.Object obj) :: JSON.Result TagInfo of
               JSON.Success tagInfo -> Just $ tiCommitSha tagInfo
               _ -> Nothing
           _ -> Nothing
    
    matchesTag :: String -> JSON.Value -> Bool
    matchesTag target (JSON.Object obj) =
      case JSON.fromJSON (JSON.Object obj) :: JSON.Result TagInfo of
        JSON.Success tagInfo -> tiName tagInfo == target
        _ -> False
    matchesTag _ _ = False

-- | Download repository archive from GitHub
downloadArchive :: GitHubRepo -> String -> IO (Either PackageError (LBS.ByteString, Integer))
downloadArchive repo commitSha = do
  let url = "https://api.github.com/repos/" ++ ghOwner repo ++ "/" ++ ghName repo ++ "/zipball/" ++ commitSha
  request <- parseRequest url
  let requestWithHeaders = setRequestHeaders
        [ ("User-Agent", "bend-package-manager")
        , ("Accept", "application/vnd.github.v3+json")
        ] request
  
  result <- try $ httpLBS requestWithHeaders :: IO (Either HttpException (Response LBS.ByteString))
  case result of
    Left ex -> return $ Left $ NetworkError $ show ex
    Right response -> do
      let status = getResponseStatusCode response
      if status == 200 || status == 302
        then do
          let body = getResponseBody response
          let size = fromIntegral $ LBS.length body
          return $ Right (body, size)
        else if status == 404
          then return $ Left $ NotFound $ "Archive not found for " ++ ghOwner repo ++ "/" ++ ghName repo
        else return $ Left $ NetworkError $ "Failed to download archive: " ++ show status

-- | Extract a zip archive to a directory
extractArchive :: LBS.ByteString -> FilePath -> IO (Either PackageError FilePath)
extractArchive archiveData targetDir = do
  result <- try $ do
    let archive = Zip.toArchive archiveData
    Zip.extractFilesFromArchive [Zip.OptDestination targetDir] archive
    -- GitHub archives have a top-level directory like owner-repo-sha/
    -- Find it and return its path
    contents <- listDirectory targetDir
    case contents of
      [singleDir] -> do
        let fullPath = targetDir </> singleDir
        isDir <- doesDirectoryExist fullPath
        if isDir
          then return fullPath
          else return targetDir
      _ -> return targetDir
  case result of
    Left (ex :: SomeException) -> return $ Left $ ExtractionError $ show ex
    Right path -> return $ Right path

-- JSON parsing helpers

data CommitRef = CommitRef { crSha :: String }

instance JSON.FromJSON CommitRef where
  parseJSON (JSON.Object v) = do
    commit <- v .: "commit"
    CommitRef <$> commit .: "sha"
  parseJSON _ = fail "Expected object for CommitRef"

data TagInfo = TagInfo
  { tiName :: String
  , tiCommitSha :: String
  }

instance JSON.FromJSON TagInfo where
  parseJSON (JSON.Object v) = do
    name <- v .: "name"
    commit <- v .: "commit"
    sha <- commit .: "sha"
    return $ TagInfo name sha
  parseJSON _ = fail "Expected object for TagInfo"

instance JSON.FromJSON RepoInfo where
  parseJSON (JSON.Object v) = do
    defaultBranch <- v .: "default_branch"
    description <- v .:? "description"
    return $ RepoInfo defaultBranch description
  parseJSON _ = fail "Expected object for RepoInfo"

instance JSON.FromJSON CommitInfo where
  parseJSON (JSON.Object v) = do
    sha <- v .: "sha"
    commit <- v .: "commit"
    message <- commit .: "message"
    return $ CommitInfo sha message
  parseJSON _ = fail "Expected object for CommitInfo"