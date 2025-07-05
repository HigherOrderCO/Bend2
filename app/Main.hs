module Main where

import Control.Monad (unless)
import qualified Data.Map as M
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Core.CLI (processFile, processFileToJS, processFileToHVM, processFileToHVMRun, listDependencies, parseFile)

-- | Show usage information
showUsage :: IO ()
showUsage = do
  putStrLn "Usage: bend <file.bend> [options]"
  putStrLn ""
  putStrLn "Options:"
  putStrLn "  --to-javascript    Compile to JavaScript"
  putStrLn "  --to-hvm           Compile to HVM"
  putStrLn "  --list-dependencies List all dependencies (recursive)"

-- | Main entry point
main :: IO ()
main = do
  args <- getArgs
  case args of
    [file, "--to-javascript"]     | isbend file -> processFileToJS file
    [file, "--to-hvm"]            | isbend file -> processFileToHVM file
    ["--to-hvm", file]            | isbend file -> processFileToHVM file
    ["--run-hvm", file]           | isbend file -> processFileToHVMRun file
    [file, "--list-dependencies"] | isbend file -> listDependencies file
    [file] | isbend file -> processFile file
    otherwise                             -> showUsage
  where
    isbend file = ".bend" `isSuffixOf` file || ".bend.py" `isSuffixOf` file
    isSuffixOf suffix str = reverse suffix == take (length suffix) (reverse str)
