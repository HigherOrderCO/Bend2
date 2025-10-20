{-# LANGUAGE OverloadedStrings #-}

module Package.Publish
  ( AuthMode(..)
  , runPublishCommand
  , runBumpCommand
  ) where

import Control.Exception (SomeException, try)
import Control.Monad (forM, forM_, unless, when)
import qualified Data.Aeson as Aeson
import Data.Aeson ((.:), (.:?))
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as LBS
import Data.Char (toLower)
import Data.Either (partitionEithers)
import Data.List (find, foldl', maximumBy, sort, sortOn, isPrefixOf)
import Data.Maybe (catMaybes)
import Data.Ord (comparing)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
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
  , renameDirectory
  )
import System.FilePath
  ( takeExtension
  , takeFileName
  , makeRelative
  , (</>)
  )
import qualified System.FilePath as FP
import System.IO (hFlush, stdout)
import Text.Read (readMaybe)

import Core.Import (ensureBendRoot)
import Package.Auth (AuthMode(..), AuthSession(..), AuthUser(..), ensureAuthenticated)
import Package.Index

data ModuleCandidate = ModuleCandidate
  { mcFullName  :: String    -- e.g. "Math=3"
  , mcBaseName  :: String    -- e.g. "Math"
  , mcVersion   :: Int       -- e.g. 3
  , mcDirectory :: FilePath
  , mcFiles     :: [LocalFile]
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

runPublishCommand :: AuthMode -> Maybe String -> IO ()
runPublishCommand authMode targetModule = do
  root <- ensureBendRoot
  rootCanonical <- canonicalizePath root
  indexCfg <- defaultIndexConfig rootCanonical
  session <- ensureAuthenticated authMode indexCfg

  let ownerRaw = auUsername (asUser session)
      ownerDir = rootCanonical </> ("@" ++ ownerRaw)

  exists <- doesDirectoryExist ownerDir
  unless exists $
    fail $ "No directory found for @" ++ ownerRaw ++ ". Expected: " ++ ownerDir

  (modules, invalids) <- discoverModules rootCanonical ownerRaw ownerDir
  unless (null invalids) $ do
    fail $ unlines
      ( "Found module directories without version suffix:"
      : map (\name -> "  - " ++ name ++ " (rename to " ++ name ++ "=0)") invalids
      )

  when (null modules) $
    fail "No publishable modules found under your BendRoot directory."

  modulesToPublish <- case targetModule of
    Nothing -> pure modules
    Just raw -> do
      mc <- selectModule modules raw
      pure [mc]

  putStrLn ""
  let shouldConfirm = length modulesToPublish == 1
  results <- forM modulesToPublish $ \moduleCand -> do
    putStrLn $ "Preparing to publish @" ++ ownerRaw ++ "/" ++ mcFullName moduleCand
    forM_ (mcFiles moduleCand) $ \lf ->
      putStrLn $ "  - " ++ lfRelative lf
    confirmed <- if shouldConfirm
                   then promptConfirmation
                   else pure True
    if not confirmed
      then pure (Left "Publish aborted by user.")
      else publishModule indexCfg session ownerRaw moduleCand

  let (errors, successes) = partitionEithers results
  when (not (null successes)) $ do
    putStrLn ""
    forM_ successes $ \resp -> do
      putStrLn $ "Successfully published " ++ prPackage resp ++ " version " ++ show (prVersion resp)
      putStrLn $ "Storage path: " ++ prStoragePath resp
  unless (null errors) $ fail (unlines errors)

runBumpCommand :: AuthMode -> String -> IO ()
runBumpCommand authMode rawModule = do
  root <- ensureBendRoot
  rootCanonical <- canonicalizePath root
  indexCfg <- defaultIndexConfig rootCanonical
  session <- ensureAuthenticated authMode indexCfg

  let ownerRaw = auUsername (asUser session)
      ownerDir = rootCanonical </> ("@" ++ ownerRaw)

  exists <- doesDirectoryExist ownerDir
  unless exists $
    fail $ "No directory found for @" ++ ownerRaw ++ ". Expected: " ++ ownerDir

  (modules, invalids) <- discoverModules rootCanonical ownerRaw ownerDir
  unless (null invalids) $ do
    fail $ unlines
      ( "Found module directories without version suffix:"
      : map (\name -> "  - " ++ name ++ " (rename to " ++ name ++ "=0)") invalids
      )

  when (null modules) $
    fail "No versioned modules found under your BendRoot directory."

  moduleCand <- selectModule modules rawModule

  let moduleBase = mcBaseName moduleCand
      currentVersion = mcVersion moduleCand

  latest <- fetchLatestVersion indexCfg session (ownerRaw, moduleBase)
  let nextLocal = currentVersion + 1
      remoteNext = maybe nextLocal (+ 1) latest
      newVersion = max nextLocal remoteNext
      newFullName = moduleBase ++ "=" ++ show newVersion
      newDir = ownerDir </> newFullName

  existsNew <- doesDirectoryExist newDir
  when existsNew $
    fail $ "Directory '" ++ newFullName ++ "' already exists. Clean it up or choose a different version."

  putStrLn $ "Renaming @" ++ ownerRaw ++ "/" ++ mcFullName moduleCand
           ++ " -> @" ++ ownerRaw ++ "/" ++ newFullName

  renameDirectory (mcDirectory moduleCand) newDir
  changed <- rewriteModuleReferences rootCanonical ownerRaw moduleBase currentVersion newVersion newDir

  if null changed
    then putStrLn "No references needed updating."
    else do
      putStrLn "Updated references in:"
      forM_ changed $ \fp -> putStrLn $ "  - " ++ fp

  putStrLn $ "Bumped @" ++ ownerRaw ++ "/" ++ moduleBase ++ " to version =" ++ show newVersion
           ++ "."
  putStrLn $ "Next steps: run 'bend publish " ++ moduleBase ++ "' to publish the new version."

discoverModules :: FilePath -> String -> FilePath -> IO ([ModuleCandidate], [String])
discoverModules root _ ownerDir = do
  entries <- sort <$> listDirectory ownerDir
  classified <- forM entries $ \entry -> do
    let moduleDir = ownerDir </> entry
    isDir <- doesDirectoryExist moduleDir
    if not isDir || "." `isPrefixOf` entry
      then pure Nothing
      else case parseModuleDirName entry of
        Nothing -> pure (Just (Left entry))
        Just (base, version) -> do
          files <- listBendFiles moduleDir
          if null files
            then pure Nothing
            else do
              localFiles <- mapM (toLocalFile root) files
              let candidate = ModuleCandidate
                    { mcFullName = entry
                    , mcBaseName = base
                    , mcVersion = version
                    , mcDirectory = moduleDir
                    , mcFiles = sortOn lfRelative localFiles
                    }
              pure (Just (Right candidate))
  let invalids = [name | Just (Left name) <- classified]
      modules  = [cand | Just (Right cand) <- classified]
  pure (modules, invalids)

parseModuleDirName :: String -> Maybe (String, Int)
parseModuleDirName name =
  case span (/= '=') name of
    (base, '=':verStr)
      | not (null base)
      , '=' `notElem` verStr
      , Just ver <- readMaybe verStr
      , ver >= 0
      -> Just (base, ver)
    _ -> Nothing

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

data ModuleRef = ModuleRef
  { mrBase     :: String
  , mrVersion  :: Maybe Int
  } deriving (Show, Eq)

parseModuleRef :: String -> Maybe ModuleRef
parseModuleRef input =
  case span (/= '=') input of
    (base, '=':verStr)
      | not (null base)
      , '=' `notElem` verStr
      , Just ver <- readMaybe verStr
      , ver >= 0
      -> Just (ModuleRef base (Just ver))
    (base, "") | not (null base) -> Just (ModuleRef base Nothing)
    _ -> Nothing

selectModule :: [ModuleCandidate] -> String -> IO ModuleCandidate
selectModule modules raw =
  case parseModuleRef raw of
    Nothing -> fail $ "Invalid module name: " ++ raw
    Just (ModuleRef base maybeVer) -> do
      let matches = filter ((== base) . mcBaseName) modules
      when (null matches) $
        fail $ "Module '" ++ base ++ "' not found under your BendRoot directory."
      case maybeVer of
        Nothing ->
          pure $ maximumBy (comparing mcVersion) matches
        Just v ->
          case find ((== v) . mcVersion) matches of
            Just cand -> pure cand
            Nothing   -> fail $ "Module '" ++ base ++ "=" ++ show v ++ "' not found."

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

fetchLatestVersion :: IndexConfig -> AuthSession -> (String, String) -> IO (Maybe Int)
fetchLatestVersion cfg session (ownerRaw, packageName) = do
  let url = apiBaseUrl cfg ++ "/api/packages/" ++ ownerRaw ++ "/" ++ packageName
  request' <- parseRequest ("GET " ++ url)
  let cookieHeader = "connect.sid=" ++ asCookie session
      request = addRequestHeader "Cookie" (BSC.pack cookieHeader) request'
  response <- httpLBS request
  let status = getResponseStatusCode response
  case status of
    200 -> case Aeson.eitherDecode (getResponseBody response) of
      Left _        -> pure Nothing
      Right details -> pure (pdLatestVersion (details :: PackageDetails))
    404 -> pure Nothing
    401 -> fail "Authentication failed while fetching package info."
    _   -> fail $ "Unexpected response while fetching package info: HTTP " ++ show status

publishModule
  :: IndexConfig
  -> AuthSession
  -> String          -- ^ owner name
  -> ModuleCandidate
  -> IO (Either String PublishResponse)
publishModule cfg session ownerRaw candidate = do
  let moduleBase = mcBaseName candidate
      version    = mcVersion candidate
      fullName   = mcFullName candidate
  latest <- fetchLatestVersion cfg session (ownerRaw, moduleBase)
  case latest of
    Just v | v >= version -> do
      let msg = "Error: module " ++ fullName ++ " already published; run 'bend bump "
                ++ moduleBase ++ "' to create a new version."
      pure (Left msg)
    _ -> do
      let packageBase = "@" ++ ownerRaw ++ "/" ++ moduleBase ++ "=" ++ show version ++ "/"
          canonicalPaths =
            map (packageBase ++) (map (relativeWithinPackage (mcDirectory candidate)) (mcFiles candidate))
      fileParts <- forM (mcFiles candidate) $ \localFile -> do
        content <- BS.readFile (lfAbsolute localFile)
        let fileName = takeFileName (lfAbsolute localFile)
        pure $ partFileRequestBody "files" fileName (RequestBodyBS content)

      let versionPart = partBS "version" (BSC.pack (show version))
          pathsPart = partLBS "paths" (Aeson.encode canonicalPaths)
          parts = versionPart : pathsPart : fileParts
          url = apiBaseUrl cfg ++ "/api/publish/@" ++ ownerRaw ++ "/" ++ moduleBase

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

rewriteModuleReferences :: FilePath -> String -> String -> Int -> Int -> FilePath -> IO [String]
rewriteModuleReferences rootDir owner base oldVersion newVersion moduleDir = do
  bendFiles <- listBendFiles moduleDir
  let oldRefs =
        [ T.pack ("@" ++ owner ++ "/" ++ base ++ "=" ++ show oldVersion)
        , T.pack ("@" ++ owner ++ "/" ++ base ++ "$" ++ show oldVersion)
        ]
      newRef = T.pack ("@" ++ owner ++ "/" ++ base ++ "=" ++ show newVersion)
  changed <- forM bendFiles $ \file -> do
    content <- TIO.readFile file
    let updated = foldl' (\acc ref -> T.replace ref newRef acc) content oldRefs
    if content == updated
      then pure Nothing
      else do
        TIO.writeFile file updated
        pure (Just (toPosix (FP.makeRelative rootDir file)))
  pure (catMaybes changed)

toPosix :: FilePath -> FilePath
toPosix path =
  let normalized = FP.normalise path
      replaced = map (\c -> if c == FP.pathSeparator then '/' else c) normalized
  in dropWhile (== '/') (dropDotSlash replaced)
  where
    dropDotSlash ('.':'/':rest) = dropDotSlash rest
    dropDotSlash other          = other
