module Package.Types where

import Data.Time (UTCTime)

-- | Represents a GitHub repository reference
data GitHubRepo = GitHubRepo
  { ghOwner :: String      -- ^ Repository owner (user or organization)
  , ghName  :: String      -- ^ Repository name
  , ghRef   :: Maybe String -- ^ Optional ref (branch, tag, or commit SHA)
  } deriving (Show, Eq)

-- | Parse a GitHub URL or shorthand into GitHubRepo
-- Supports formats:
--   - https://github.com/owner/repo
--   - gh:owner/repo
--   - gh:owner/repo@ref
parseGitHubRef :: String -> Either String GitHubRepo
parseGitHubRef url
  | "https://github.com/" `isPrefixOf` url = parseFullURL (drop 19 url)
  | "gh:" `isPrefixOf` url = parseShorthand (drop 3 url)
  | otherwise = Left $ "Invalid GitHub reference: " ++ url
  where
    isPrefixOf :: String -> String -> Bool
    isPrefixOf [] _ = True
    isPrefixOf _ [] = False
    isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys
    
    parseFullURL :: String -> Either String GitHubRepo
    parseFullURL path = 
      case break (== '/') path of
        (owner, '/':rest) -> 
          let name = takeWhile (/= '/') $ dropGitSuffix rest
          in Right $ GitHubRepo owner name Nothing
        _ -> Left $ "Invalid GitHub URL format"
    
    parseShorthand :: String -> Either String GitHubRepo
    parseShorthand path =
      case break (== '/') path of
        (owner, '/':rest) ->
          case break (== '@') rest of
            (name, '@':ref) -> Right $ GitHubRepo owner name (Just ref)
            (name, "") -> Right $ GitHubRepo owner name Nothing
            _ -> Left $ "Invalid shorthand format"
        _ -> Left $ "Invalid shorthand format: missing /"
    
    dropGitSuffix :: String -> String
    dropGitSuffix s
      | ".git" `isSuffixOf` s = take (length s - 4) s
      | otherwise = s
      where
        isSuffixOf suffix str = 
          length str >= length suffix && 
          drop (length str - length suffix) str == suffix

-- | Result of downloading a repository
data DownloadResult = DownloadResult
  { drRepo       :: GitHubRepo    -- ^ Repository that was downloaded
  , drCommitHash :: String        -- ^ Actual commit SHA that was downloaded
  , drFilePath   :: FilePath      -- ^ Path to downloaded/extracted content
  , drSize       :: Integer       -- ^ Total size in bytes
  } deriving (Show)

-- | Package metadata stored in cache
data PackageMetadata = PackageMetadata
  { pmSource      :: GitHubRepo   -- ^ Source repository
  , pmCommit      :: String        -- ^ Commit hash
  , pmDownloaded  :: UTCTime      -- ^ When it was downloaded
  , pmContentHash :: String        -- ^ SHA256 of package contents
  , pmBendFiles   :: [FilePath]   -- ^ List of .bend files found
  } deriving (Show)

-- | Errors that can occur during package operations
data PackageError
  = NetworkError String           -- ^ HTTP/network errors
  | ParseError String             -- ^ Parsing errors
  | NotFound String              -- ^ Repository or ref not found
  | RateLimited Int              -- ^ GitHub rate limit hit (reset time)
  | ExtractionError String       -- ^ Archive extraction failed
  | ValidationError String       -- ^ Package validation failed
  deriving (Show, Eq)

-- | API response for repository info
data RepoInfo = RepoInfo
  { riDefaultBranch :: String
  , riDescription   :: Maybe String
  } deriving (Show)

-- | API response for commit info
data CommitInfo = CommitInfo
  { ciSha     :: String
  , ciMessage :: String
  } deriving (Show)