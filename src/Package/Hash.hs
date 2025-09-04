{-# LANGUAGE OverloadedStrings #-}

module Package.Hash where

import Package.Types

import Control.Monad (forM, filterM)
import Crypto.Hash (SHA256, hashWith)
import qualified Crypto.Hash as Hash
import qualified Data.ByteArray as BA
import qualified Data.ByteArray.Encoding as BAE
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Data.List (sort, isSuffixOf)
import Data.Time (getCurrentTime)
import System.Directory
import System.FilePath
import Text.Printf (printf)

-- | Hash all .bend files in a directory to create a content hash
hashPackageContents :: FilePath -> IO String
hashPackageContents dir = do
  bendFiles <- findBendFiles dir
  if null bendFiles
    then return "empty-package"
    else do
      -- Sort files for deterministic hashing
      let sortedFiles = sort bendFiles
      -- Hash each file's path and contents
      hashes <- forM sortedFiles $ \file -> do
        content <- BS.readFile file
        let relPath = makeRelative dir file
        return $ hashFileWithPath relPath content
      -- Combine all hashes
      let combinedHash = mconcat hashes
      return $ bytesToHex combinedHash

-- | Find all .bend files recursively in a directory
findBendFiles :: FilePath -> IO [FilePath]
findBendFiles dir = do
  exists <- doesDirectoryExist dir
  if not exists
    then return []
    else do
      contents <- listDirectory dir
      let paths = map (dir </>) contents
      files <- filterM doesFileExist paths
      let bendFiles = filter (\f -> ".bend" `isSuffixOf` f) files
      dirs <- filterM doesDirectoryExist paths
      subFiles <- concat <$> mapM findBendFiles dirs
      return $ bendFiles ++ subFiles

-- | Hash a file with its relative path
hashFileWithPath :: FilePath -> BS.ByteString -> BS.ByteString
hashFileWithPath path content =
  let pathBS = BSC.pack path
      combined = BS.append pathBS content
      digest = hashWith Hash.SHA256 combined
      hexDigest = BAE.convertToBase BAE.Base16 digest :: BS.ByteString
  in hexDigest

-- | Convert ByteString to hex string
bytesToHex :: BS.ByteString -> String
bytesToHex = BSC.unpack

-- | Create package metadata from a downloaded repository
createPackageMetadata :: DownloadResult -> IO PackageMetadata
createPackageMetadata result = do
  bendFiles <- findBendFiles (drFilePath result)
  contentHash <- hashPackageContents (drFilePath result)
  now <- getCurrentTime
  let relBendFiles = map (makeRelative (drFilePath result)) bendFiles
  return $ PackageMetadata
    { pmSource = drRepo result
    , pmCommit = drCommitHash result
    , pmDownloaded = now
    , pmContentHash = contentHash
    , pmBendFiles = relBendFiles
    }

-- | Verify package integrity by comparing hashes
verifyPackage :: FilePath -> String -> IO Bool
verifyPackage dir expectedHash = do
  actualHash <- hashPackageContents dir
  return $ actualHash == expectedHash