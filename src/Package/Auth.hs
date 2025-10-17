{-# LANGUAGE OverloadedStrings #-}

module Package.Auth
  ( AuthSession(..)
  , AuthUser(..)
  , AuthMode(..)
  , ensureAuthenticated
  ) where

import Control.Applicative ((<|>))
import Control.Concurrent (threadDelay)
import Control.Exception (SomeException, try)
import Control.Monad (unless, void, when)
import Data.Aeson (FromJSON (..), eitherDecode')
import qualified Data.Aeson as Aeson
import Data.Aeson ((.:), (.:?))
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as LBS
import Data.Char (isSpace)
import Data.Foldable (asum)
import Data.Maybe (fromMaybe)
import Data.Time.Clock (UTCTime, addUTCTime, diffUTCTime, getCurrentTime)
import qualified Data.Text as T
import Network.HTTP.Client (Response)
import Network.HTTP.Simple
import System.Directory
  ( createDirectoryIfMissing
  , doesFileExist
  , getHomeDirectory
  )
import System.FilePath (takeDirectory, (</>))
import System.Info (os)
import System.IO (hFlush, stdout)
import System.Process (callCommand, callProcess)

import Package.Index (IndexConfig (..))

data AuthSession = AuthSession
  { asCookie :: String
  , asUser   :: AuthUser
  } deriving (Show, Eq)

data AuthUser = AuthUser
  { auUsername    :: String
  , auDisplayName :: Maybe String
  } deriving (Show, Eq)

instance FromJSON AuthUser where
  parseJSON v = parseDirect v <|> parseWrapped v
    where
      parseDirect = Aeson.withObject "AuthUser" $ \o -> do
        username <- asum
          [ o Aeson..:? "username"
          , o Aeson..:? "login"
          , o Aeson..:? "githubUsername"
          ]
        case username of
          Nothing -> fail "Missing username field in auth response."
          Just u  -> AuthUser u <$> o Aeson..:? "name"
      parseWrapped = Aeson.withObject "AuthUserWrapper" $ \o -> do
        inner <- o .: "user"
        parseJSON inner

data StoredSession = StoredSession
  { ssCookie   :: String
  , ssUsername :: Maybe String
  } deriving (Show, Eq)

instance FromJSON StoredSession where
  parseJSON = Aeson.withObject "StoredSession" $ \o ->
    StoredSession <$> o Aeson..: "cookie"
                  <*> o Aeson..:? "username"

instance Aeson.ToJSON StoredSession where
  toJSON (StoredSession cookie username) =
    Aeson.object
      [ "cookie" Aeson..= cookie
      , "username" Aeson..= username
      ]

data DeviceStart = DeviceStart
  { dsDeviceCode      :: String
  , dsUserCode        :: String
  , dsVerificationUrl :: String
  , dsPollInterval    :: Int
  , dsExpiresIn       :: Int
  } deriving (Show, Eq)

instance FromJSON DeviceStart where
  parseJSON = Aeson.withObject "DeviceStart" $ \o ->
    DeviceStart <$> o .: "deviceCode"
                <*> o .: "userCode"
                <*> o .: "verificationUrl"
                <*> o .: "pollInterval"
                <*> o .: "expiresIn"

data DevicePoll
  = PollPending
  | PollSlowDown (Maybe Int)
  | PollApproved String AuthUser
  | PollDenied (Maybe String)
  | PollExpired (Maybe String)
  deriving (Show, Eq)

instance FromJSON DevicePoll where
  parseJSON = Aeson.withObject "DevicePoll" $ \o -> do
    status <- o .: "status"
    case (status :: String) of
      "pending"    -> pure PollPending
      "slow_down"  -> PollSlowDown <$> o .:? "pollInterval"
      "approved"   -> PollApproved <$> o .: "sessionCookie" <*> o .: "user"
      "denied"     -> PollDenied <$> o .:? "message"
      "expired"    -> PollExpired <$> o .:? "message"
      other        -> fail ("Unknown device poll status: " ++ other)

data AuthMode = AuthAuto | AuthManual
  deriving (Eq, Show)

ensureAuthenticated :: AuthMode -> IndexConfig -> IO AuthSession
ensureAuthenticated mode cfg = do
  stored <- loadStoredSession
  case stored of
    Just sess -> do
      result <- validateSession cfg (ssCookie sess)
      case result of
        Right user -> pure (AuthSession (ssCookie sess) user)
        Left _ -> do
          putStrLn "Stored Bend session expired. Re-authenticating..."
          interactiveLogin mode cfg
    Nothing -> interactiveLogin mode cfg

interactiveLogin :: AuthMode -> IndexConfig -> IO AuthSession
interactiveLogin mode cfg = do
  putStrLn "Authentication required."
  case mode of
    AuthManual -> manualCookieLogin cfg
    AuthAuto -> do
      deviceResult <- runDeviceFlow cfg
      case deviceResult of
        Right session -> pure session
        Left deviceErr -> do
          putStrLn $ "Device login failed: " ++ deviceErr
          putStrLn "Falling back to manual cookie entry."
          manualCookieLogin cfg

runDeviceFlow :: IndexConfig -> IO (Either String AuthSession)
runDeviceFlow cfg = do
  startResp <- startDeviceFlow cfg
  case startResp of
    Left err -> pure (Left err)
    Right info -> do
      putStrLn ""
      putStrLn "Follow the instructions below to authorize Bend:"
      putStrLn $ "  Verification URL: " ++ dsVerificationUrl info
      putStrLn $ "  User Code:        " ++ dsUserCode info
      openBrowser (dsVerificationUrl info)
      deadline <- addUTCTime (fromIntegral (dsExpiresIn info)) <$> getCurrentTime
      pollForApproval cfg info (max 1 (dsPollInterval info)) deadline

startDeviceFlow :: IndexConfig -> IO (Either String DeviceStart)
startDeviceFlow cfg = do
  let url = apiBaseUrl cfg ++ "/auth/device/start"
  requestBase <- parseRequest url
  let request = setRequestMethod "POST" requestBase
  result <- try (httpLBS request) :: IO (Either SomeException (Response LBS.ByteString))
  case result of
    Left err -> pure (Left ("Network error: " ++ show err))
    Right response -> do
      let status = getResponseStatusCode response
      if status == 200
        then pure $ eitherDecode' (getResponseBody response)
        else pure $ Left ("HTTP " ++ show status)

pollForApproval
  :: IndexConfig
  -> DeviceStart
  -> Int
  -> UTCTime
  -> IO (Either String AuthSession)
pollForApproval cfg info interval deadline = do
  now <- getCurrentTime
  if now >= deadline
    then pure (Left "Device code expired before authorization.")
    else do
      pollResult <- pollDeviceFlow cfg (dsDeviceCode info)
      case pollResult of
        Left err -> do
          putStrLn $ "Polling error: " ++ err
          waitWithDeadline interval deadline
          pollForApproval cfg info interval deadline
        Right PollPending -> do
          waitWithDeadline interval deadline
          pollForApproval cfg info interval deadline
        Right (PollSlowDown newInterval) -> do
          let nextInterval = max 1 (fromMaybe (interval + 1) newInterval)
          waitWithDeadline nextInterval deadline
          pollForApproval cfg info nextInterval deadline
        Right (PollApproved cookie user) -> do
          let normalizedCookie = normalizeCookie cookie
          storeSession normalizedCookie (auUsername user)
          pure (Right (AuthSession normalizedCookie user))
        Right (PollDenied msg) ->
          pure (Left (fromMaybe "Authentication denied." msg))
        Right (PollExpired msg) ->
          pure (Left (fromMaybe "Device code expired." msg))

pollDeviceFlow :: IndexConfig -> String -> IO (Either String DevicePoll)
pollDeviceFlow cfg deviceCode = do
  let baseUrl = apiBaseUrl cfg ++ "/auth/device/poll"
  requestBase <- parseRequest baseUrl
  let request = setRequestQueryString [("code", Just (BSC.pack deviceCode))] requestBase
  result <- try (httpLBS request) :: IO (Either SomeException (Response LBS.ByteString))
  case result of
    Left err -> pure (Left ("Network error: " ++ show err))
    Right response -> do
      let status = getResponseStatusCode response
      if status == 200
        then pure $ eitherDecode' (getResponseBody response)
        else pure $ Left ("HTTP " ++ show status)

waitWithDeadline :: Int -> UTCTime -> IO ()
waitWithDeadline seconds deadline = do
  now <- getCurrentTime
  let remaining = realToFrac (diffUTCTime deadline now) :: Double
      waitSeconds = min remaining (fromIntegral seconds)
  when (waitSeconds > 0) $
    threadDelay (floor (waitSeconds * 1000000))

openBrowser :: String -> IO ()
openBrowser url =
  case os of
    "darwin" -> void (try (callProcess "open" [url]) :: IO (Either SomeException ()))
    "linux"  -> void (try (callProcess "xdg-open" [url]) :: IO (Either SomeException ()))
    "mingw32" -> void (try (callCommand ("start \"\" \"" ++ url ++ "\"")) :: IO (Either SomeException ()))
    _        -> pure ()

manualCookieLogin :: IndexConfig -> IO AuthSession
manualCookieLogin cfg = do
  putStrLn ""
  putStrLn "Manual login instructions:"
  putStrLn $ "  1. Open: " ++ apiBaseUrl cfg ++ "/auth/github"
  putStrLn "  2. Complete the GitHub authorization."
  putStrLn "  3. Copy the value of the `connect.sid` cookie and paste it below."
  putStr   "Cookie value: "
  hFlush stdout
  cookieInput <- trim <$> getLine
  when (null cookieInput) $
    fail "Authentication aborted."
  let cookieValue = normalizeCookie cookieInput
  validation <- validateSession cfg cookieValue
  case validation of
    Left err -> fail ("Failed to validate session: " ++ err)
    Right user -> do
      let normalized = normalizeCookie cookieValue
      storeSession normalized (auUsername user)
      pure (AuthSession normalized user)

validateSession :: IndexConfig -> String -> IO (Either String AuthUser)
validateSession cfg cookieValue = do
  let url = apiBaseUrl cfg ++ "/auth/me"
  requestBase <- parseRequest ("GET " ++ url)
  let cookieHeader = "connect.sid=" ++ cookieValue
      request = addRequestHeader "Cookie" (BSC.pack cookieHeader) requestBase
  response <- httpLBS request
  let status = getResponseStatusCode response
  if status == 200
    then pure $ eitherDecode' (getResponseBody response)
    else pure $ Left ("HTTP " ++ show status)

loadStoredSession :: IO (Maybe StoredSession)
loadStoredSession = do
  path <- sessionFilePath
  exists <- doesFileExist path
  if not exists
    then pure Nothing
    else do
      contents <- LBS.readFile path
      pure (either (const Nothing) Just (eitherDecode' contents))

storeSession :: String -> String -> IO ()
storeSession cookie username = do
  path <- sessionFilePath
  createDirectoryIfMissing True (takeDirectory path)
  let payload = StoredSession cookie (Just username)
  LBS.writeFile path (Aeson.encode payload)

sessionFilePath :: IO FilePath
sessionFilePath = do
  home <- getHomeDirectory
  pure (home </> ".bend" </> "session.json")

trim :: String -> String
trim = f . f
  where
    f = reverse . dropWhile isSpace

normalizeCookie :: String -> String
normalizeCookie raw =
  let stripped = trim raw
  in case T.stripPrefix "connect.sid=" (T.pack stripped) of
       Just rest -> T.unpack rest
       Nothing   -> stripped
