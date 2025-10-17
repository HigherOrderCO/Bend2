{-# LANGUAGE OverloadedStrings #-}

module Package.Publish
  ( runPublishCommand
  , AuthMode(..)
  ) where

import Control.Exception (SomeException, try)
import Control.Monad (forM, forM_, unless, when)
import qualified Data.Aeson as Aeson
import Data.Aeson ((.:), (.:?))
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as LBS
import Data.List (sort, sortOn, isPrefixOf)
import Data.Maybe (catMaybes)
import Data.Char (toLower)
import Network.HTTP.Client (RequestBody (RequestBodyBS))
import Network.HTTP.Client.MultipartFormData
  ( formDataBody
  , partBS
  , partFileRequestBody
  , partLBS
  )
import Network.HTTP.Simple
import System.Directory
  ( doesDirectoryExist
  , doesFileExist
  , listDirectory
  , canonicalizePath
  )
import System.FilePath
  ( takeExtension
  , takeFileName
  , makeRelative
  , (</>)
  )
import qualified System.FilePath as FP
import System.IO (hFlush, stdout)
import Text.Printf (printf)
import Text.Read (readMaybe)

import Core.Import (ensureBendRoot)
import Package.Auth (AuthMode(..), AuthSession(..), AuthUser(..), ensureAuthenticated)
import Package.Index

data PackageCandidate = PackageCandidate
  { pcName      :: String
  , pcDirectory :: FilePath
  , pcFiles     :: [LocalFile]
  } deriving (Show, Eq)

data LocalFile = LocalFile
  { lfAbsolute :: FilePath
  , lfRelative :: FilePath   -- ^ BendRoot-relative (POSIX separators)
  } deriving (Show, Eq)

data PackageDetails = PackageDetails
  { pdLatestVersion :: Maybe Int
  } deriving (Show, Eq)

instance Aeson.FromJSON PackageDetails where
  parseJSON = Aeson.withObject "PackageDetailsWrapper" $ \o -> do
    inner <- o .: "package"
    PackageDetails <$> inner .:? "latest_version"

data PublishResponse = PublishResponse
  { prPackage     :: String
  , prVersion     :: Int
  , prStoragePath :: String
  } deriving (Show, Eq)

instance Aeson.FromJSON PublishResponse where
  parseJSON = Aeson.withObject "PublishResponse" $ \o ->
    PublishResponse <$> o .: "package"
                    <*> o .: "version"
                    <*> o .: "storage_path"

data ErrorResponse = ErrorResponse
  { erError   :: String
  , erDetails :: Maybe String
  } deriving (Show, Eq)

instance Aeson.FromJSON ErrorResponse where
  parseJSON = Aeson.withObject "ErrorResponse" $ \o ->
    ErrorResponse <$> o .: "error"
                  <*> o .:? "details"

runPublishCommand :: AuthMode -> IO ()
runPublishCommand authMode = do
  root <- ensureBendRoot
  rootCanonical <- canonicalizePath root
  indexCfg <- defaultIndexConfig rootCanonical
  session <- ensureAuthenticated authMode indexCfg
  putStrLn $ "Using session cookie: connect.sid=" ++ asCookie session

  let ownerRaw = auUsername (asUser session)
      ownerDir = rootCanonical </> ("@" ++ ownerRaw)

  exists <- doesDirectoryExist ownerDir
  unless exists $
    fail $ "No directory found for @" ++ ownerRaw ++ ". Expected: " ++ ownerDir

  candidates <- discoverPackages rootCanonical ownerRaw ownerDir
  when (null candidates) $
    fail "No publishable packages found under your BendRoot directory."

  package <- promptForPackage candidates
  let packageRaw = pcName package
  version <- determineNextVersion indexCfg session (ownerRaw, packageRaw)

  putStrLn ""
  putStrLn $ "Preparing to publish @" ++ ownerRaw ++ "/" ++ packageRaw ++ " version " ++ show version
  forM_ (pcFiles package) $ \lf ->
    putStrLn $ "  - " ++ lfRelative lf

  confirmed <- promptConfirmation
  unless confirmed $
    fail "Publish aborted by user."

  result <- publishPackage indexCfg session ownerRaw packageRaw package version

  case result of
    Left err -> fail ("Publish failed: " ++ err)
    Right resp -> do
      putStrLn ""
      putStrLn $ "Successfully published " ++ prPackage resp ++ " version " ++ show (prVersion resp)
      putStrLn $ "Storage path: " ++ prStoragePath resp

discoverPackages :: FilePath -> String -> FilePath -> IO [PackageCandidate]
discoverPackages root _ ownerDir = do
  entries <- listDirectory ownerDir
  let dirs = sort entries
  catMaybes <$> forM dirs (\entry -> do
    let packageDir = ownerDir </> entry
    if "." `isPrefixOf` entry
      then pure Nothing
      else do
        isDir <- doesDirectoryExist packageDir
        if not isDir
          then pure Nothing
          else do
            files <- listBendFiles packageDir
            if null files
              then pure Nothing
              else do
                localFiles <- mapM (toLocalFile root) files
                pure $ Just PackageCandidate
                  { pcName = entry
                  , pcDirectory = packageDir
                  , pcFiles = sortOn lfRelative localFiles
                  })

listBendFiles :: FilePath -> IO [FilePath]
listBendFiles path = do
  children <- listDirectory path
  fmap concat $ forM children $ \child -> do
    let childPath = path </> child
    isDir <- doesDirectoryExist childPath
    if isDir
      then
        if "." `isPrefixOf` child
          then pure []
          else listBendFiles childPath
      else do
        isFile <- doesFileExist childPath
        if isFile && takeExtension childPath == ".bend" && not ("." `isPrefixOf` child)
          then pure [childPath]
          else pure []

toLocalFile :: FilePath -> FilePath -> IO LocalFile
toLocalFile root file = do
  canonical <- canonicalizePath file
  let rel = makeRelative root canonical
  pure LocalFile
    { lfAbsolute = canonical
    , lfRelative = toPosix rel
    }

promptForPackage :: [PackageCandidate] -> IO PackageCandidate
promptForPackage candidates = do
  putStrLn "Select a package to publish:"
  forM_ (zip [1 :: Int ..] candidates) $ \(idx, PackageCandidate name _ files) ->
    putStrLn (printf "  [%d] %s (%d files)" idx name (length files))
  putStr "Enter choice: "
  hFlush stdout
  selection <- getLine
  case readMaybe selection of
    Just n | n >= 1 && n <= length candidates -> pure (candidates !! (n - 1))
    _ -> do
      putStrLn "Invalid choice. Please try again."
      promptForPackage candidates

promptConfirmation :: IO Bool
promptConfirmation = do
  putStr "Publish these files? [y/N]: "
  hFlush stdout
  response <- fmap (map toLower) getLine
  pure (response == "y" || response == "yes")
  where
    toLower c
      | 'A' <= c && c <= 'Z' = toEnum (fromEnum c + 32)
      | otherwise = c

determineNextVersion :: IndexConfig -> AuthSession -> (String, String) -> IO Int
determineNextVersion cfg session (ownerRaw, packageName) = do
  let url = apiBaseUrl cfg ++ "/api/packages/" ++ ownerRaw ++ "/" ++ packageName
  request' <- parseRequest ("GET " ++ url)
  let cookieHeader = "connect.sid=" ++ asCookie session
      request = addRequestHeader "Cookie" (BSC.pack cookieHeader) request'
  response <- httpLBS request
  let status = getResponseStatusCode response
  case status of
    200 -> case Aeson.eitherDecode (getResponseBody response) of
      Left _ -> pure 1
      Right details ->
        case pdLatestVersion (details :: PackageDetails) of
          Nothing -> pure 1
          Just v  -> pure (v + 1)
    404 -> pure 1
    401 -> fail "Authentication failed while fetching package info."
    _   -> fail $ "Unexpected response while fetching package info: HTTP " ++ show status

publishPackage
  :: IndexConfig
  -> AuthSession
  -> String   -- ^ owner name
  -> String   -- ^ package name
  -> PackageCandidate
  -> Int
  -> IO (Either String PublishResponse)
publishPackage cfg session ownerRaw packageRaw candidate version = do
  let packageBase = "@" ++ ownerRaw ++ "/" ++ packageRaw ++ "#" ++ show version ++ "/"
      canonicalPaths =
        map (packageBase ++) (map (relativeWithinPackage (pcDirectory candidate)) (pcFiles candidate))
  fileParts <- forM (pcFiles candidate) $ \localFile -> do
    content <- BS.readFile (lfAbsolute localFile)
    let fileName = takeFileName (lfAbsolute localFile)
    pure $ partFileRequestBody "files" fileName (RequestBodyBS content)

  let versionPart = partBS "version" (BSC.pack (show version))
      pathsPart = partLBS "paths" (Aeson.encode canonicalPaths)
      parts = versionPart : pathsPart : fileParts
      url = apiBaseUrl cfg ++ "/api/publish/@" ++ ownerRaw ++ "/" ++ packageRaw

  putStrLn "Attempting publish request:"
  putStrLn $ "  URL: " ++ url
  putStrLn $ "  Version: " ++ show version
  putStrLn $ "  Paths: " ++ show canonicalPaths

  requestBase <- parseRequest url
  let cookieHeader = "connect.sid=" ++ asCookie session
      withCookie = addRequestHeader "Cookie" (BSC.pack cookieHeader) requestBase
  requestWithBody <- formDataBody parts withCookie
  let request = setRequestMethod "PUT" requestWithBody

  result <- try (httpLBS request) :: IO (Either SomeException (Response LBS.ByteString))
  case result of
    Left err -> pure (Left ("Network error: " ++ show err))
    Right response -> do
      let status = getResponseStatusCode response
      if status == 201
        then pure $ Aeson.eitherDecode (getResponseBody response)
        else do
          putStrLn $ "Publish failed with HTTP " ++ show status
          putStrLn $ "Response body: " ++ BSC.unpack (BSC.take 500 (LBS.toStrict (getResponseBody response)))
          pure $ Left (formatErrorResponse (getResponseBody response) status)

relativeWithinPackage :: FilePath -> LocalFile -> FilePath
relativeWithinPackage packageDir localFile =
  toPosix (FP.makeRelative packageDir (lfAbsolute localFile))

formatErrorResponse :: LBS.ByteString -> Int -> String
formatErrorResponse body status =
  let parsed = Aeson.eitherDecode body :: Either String ErrorResponse
  in case parsed of
       Right err ->
         let detailText = maybe "" (\d -> " (" ++ d ++ ")") (erDetails err)
         in erError err ++ detailText
       Left _ -> "HTTP " ++ show status

toPosix :: FilePath -> FilePath
toPosix path =
  let normalized = FP.normalise path
      replaced = map (\c -> if c == FP.pathSeparator then '/' else c) normalized
  in dropWhile (== '/') (dropDotSlash replaced)
  where
    dropDotSlash ('.':'/':rest) = dropDotSlash rest
    dropDotSlash other          = other
