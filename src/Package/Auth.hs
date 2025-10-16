{-# LANGUAGE OverloadedStrings #-}

module Package.Auth
  ( AuthSession(..)
  , AuthUser(..)
  , ensureAuthenticated
  ) where

import Control.Exception (SomeException, try)
import Control.Monad (unless, when)
import Data.Aeson (FromJSON (..), eitherDecode')
import qualified Data.Aeson as Aeson
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString.Char8 as BSC
import Data.Char (isSpace)
import Data.Foldable (asum)
import Data.Maybe (fromMaybe)
import qualified Data.Text as T
import Network.HTTP.Simple
import System.Directory
  ( createDirectoryIfMissing
  , doesFileExist
  , getHomeDirectory
  )
import System.FilePath (takeDirectory, (</>))
import System.IO (hFlush, stdout)
import Package.Index (IndexConfig (..))

data AuthSession = AuthSession
  { asCookie  :: String
  , asUser    :: AuthUser
  } deriving (Show, Eq)

data AuthUser = AuthUser
  { auUsername    :: String
  , auDisplayName :: Maybe String
  } deriving (Show, Eq)

instance FromJSON AuthUser where
  parseJSON = Aeson.withObject "AuthUser" $ \o -> do
    username <- asum
      [ o Aeson..:? "username"
      , o Aeson..:? "login"
      , o Aeson..:? "githubUsername"
      ]
    case username of
      Nothing -> fail "Missing username field in /auth/me response."
      Just u  -> AuthUser u <$> o Aeson..:? "name"

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

ensureAuthenticated :: IndexConfig -> IO AuthSession
ensureAuthenticated cfg = do
  stored <- loadStoredSession
  case stored of
    Just sess -> do
      result <- validateSession cfg (ssCookie sess)
      case result of
        Right user -> pure (AuthSession (ssCookie sess) user)
        Left _ -> do
          putStrLn "Stored Bend session expired. Re-authenticating..."
          interactiveLogin cfg
    Nothing -> interactiveLogin cfg

interactiveLogin :: IndexConfig -> IO AuthSession
interactiveLogin cfg = do
  putStrLn "Authentication required."
  putStrLn $ "Please open the following URL in your browser and authenticate:\n  "
    ++ apiBaseUrl cfg ++ "/auth/github"
  putStrLn ""
  putStrLn "After completing the login, copy the `connect.sid` cookie value from your browser"
  putStr   "and paste it here: "
  hFlush stdout
  cookieInput <- trim <$> getLine
  when (null cookieInput) $ do
    putStrLn "No cookie provided; aborting."
    fail "Authentication aborted."
  let cookieValue = normalizeCookie cookieInput
  validation <- validateSession cfg cookieValue
  case validation of
    Left err -> do
      putStrLn $ "Failed to validate session: " ++ err
      fail "Authentication failed."
    Right user -> do
      storeSession cookieValue (auUsername user)
      pure (AuthSession cookieValue user)

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
