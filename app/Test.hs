module Main where

import Control.Monad (unless)
import Control.Monad.State.Lazy (evalStateT)
import qualified Data.Map as M
import System.Environment (getArgs)
import System.Exit (exitFailure)

import Core.AutoImport
import Core.Bind
import Core.Check
import Core.Normal
import Core.Type
import Core.Termination
import qualified Core.Parse as Parse

-- | Parse a Bend file into a Book
parseFile :: FilePath -> IO Book
parseFile file = do
  content <- readFile file
  case Parse.doParseBook file content of
    Left err -> do
      putStrLn $ "Parse error: " ++ err
      exitFailure
    Right book -> do
      -- Auto-import unbound references
      autoImportedBook <- autoImport (takeDirectory file) book
      return autoImportedBook
  where
    takeDirectory path = reverse . dropWhile (/= '/') . reverse $ path

-- | Type-check all definitions in a book
checkDefinitions :: Book -> IO ()
checkDefinitions book = do
  let boundBook = bindBook book
  let (Book defs) = boundBook
  success <- checkAll boundBook (M.toList defs)
  unless success exitFailure
  where
    checkAll :: Book -> [(Name, Defn)] -> IO Bool
    checkAll _ [] = return True
    checkAll bBook ((name, (term, typ)):rest) = do
      case check 0 bBook id term typ of
        Done () -> do
          putStrLn $ "\x1b[32m✓ " ++ name ++ "\x1b[0m"
          checkAll bBook rest
        Fail e -> do
          putStrLn $ "\x1b[31m✗ " ++ name ++ "\x1b[0m"
          putStrLn $ show e
          _ <- checkAll bBook rest
          return False

-- | Termination-check all definitions in a book
checkTerminations :: Book -> IO ()
checkTerminations book = do
  let boundBook = bindBook book
  let (Book defs) = boundBook
  success <- terminatesAll boundBook (M.toList defs)
  unless success exitFailure
  where
    terminatesAll :: Book -> [(Name, Defn)] -> IO Bool
    terminatesAll _ [] = return True
    terminatesAll bBook ((name, (term, typ)):rest) = do
      case terminates bBook term of
        TerminationDone () -> do
          putStrLn $ "\x1b[32m✓ " ++ name ++ "\x1b[0m"
          terminatesAll bBook rest
        TerminationFail e -> do
          putStrLn $ "\x1b[31m✗ " ++ name ++ "\x1b[0m"
          putStrLn $ show e
          _ <- terminatesAll bBook rest
          return False

-- | Run the main function from a book
runMain :: Book -> IO ()
runMain book = do
  case deref book "main" of
    Nothing -> do
      return ()
    Just _ -> do
      let boundBook = bindBook book
      let mainCall = Ref "main"
      case infer 0 boundBook id mainCall of
        Fail e -> do
          putStrLn $ "Error running main: " ++ show e
          exitFailure
        Done typ -> do
          let result = normal 2 0 boundBook mainCall
          putStrLn ""
          putStrLn "Running main:"
          putStrLn $ show result

-- | Process a Bend file: parse, check, and run
processFile :: FilePath -> IO ()
processFile file = do
  book <- parseFile file
  putStrLn "Type-checking:"
  checkDefinitions book
  putStrLn "Termination-checking:"
  checkTerminations book
  runMain book

-- | Show usage information
showUsage :: IO ()
showUsage = putStrLn "Usage: bend <file.bend>"

-- | Main entry point
main :: IO ()
main = do
  args <- getArgs
  case args of
    [file] | ".bend" `isSuffixOf` file -> processFile file
    _ -> showUsage
  where
    isSuffixOf suffix str = reverse suffix == take (length suffix) (reverse str)
