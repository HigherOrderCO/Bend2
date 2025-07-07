module Core.CLI 
  ( parseFile
  , checkDefinitions
  , runMain
  , processFile
  , processFileToJS
  , processFileToHVM
  , processFileToHVMRun
  , listDependencies
  ) where

import Control.Monad (unless, forM_)
import qualified Data.Map as M
import qualified Data.Set as S
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))
import Control.Exception (catch, IOException)

import Core.Bind
import Core.Check
import Core.Collapse
import Core.Deps
import Core.Import (autoImport)
import Core.Parse.Book (doParseBook)
import Core.Type
import Core.WHNF

import qualified Target.JavaScript as JS

-- import qualified HVM.Compile as HVM

import qualified Target.HVMtarget as HVMTarget
import System.Directory (createDirectoryIfMissing, getHomeDirectory)
import HVM.API (runHVM, RunMode (Collapse, Normalize))
import qualified HVM.Type as HVM
import Debug.Trace (trace)
import qualified Target.HVM as HVM

-- | Parse a Bend file into a Book
parseFile :: FilePath -> IO Book
parseFile file = do
  content <- readFile file
  case doParseBook file content of
    Left err -> do
      putStrLn $ err
      exitFailure
    Right book -> do
      -- Auto-import unbound references
      autoImportedBook <- autoImport (takeDirectory file) book
      return autoImportedBook
  where
    takeDirectory path = reverse . dropWhile (/= '/') . reverse $ path

-- | Type-check all definitions in a book
checkDefinitions :: Book -> IO ()
checkDefinitions book@(Book defs) = do
  success <- checkAll book (M.toList defs)
  unless success exitFailure
  where
    checkDef book term typ = do
      check 0 noSpan book (Ctx []) typ Set
      check 0 noSpan book (Ctx []) term typ
      return ()
    checkAll :: Book -> [(Name, Defn)] -> IO Bool
    checkAll _ [] = return True
    checkAll bBook ((name, (_, term, typ)):rest) = do
      case checkDef bBook term typ of
        Done () -> do
          putStrLn $ "\x1b[32m✓ " ++ name ++ "\x1b[0m"
          checkAll bBook rest
        Fail e -> do
          putStrLn $ "\x1b[31m✗ " ++ name ++ "\x1b[0m"
          putStrLn $ show e
          _ <- checkAll bBook rest
          return False

-- | Run the main function from a book
runMain :: Book -> IO ()
runMain book = do
  case deref book "main" of
    Nothing -> do
      return ()
    Just _ -> do
      let mainCall = Ref "main"
      case infer 0 noSpan book (Ctx []) mainCall of
        Fail e -> do
          putStrLn $ show e
          exitFailure
        Done typ -> do
          let results = flatten $ collapse 0 book $ normal 0 book mainCall
          putStrLn ""
          forM_ results $ \ term -> do
            print term

-- | Process a Bend file: parse, check, and run
processFile :: FilePath -> IO ()
processFile file = do
  book <- parseFile file
  checkDefinitions book
  runMain book

-- | Try to format JavaScript code using prettier if available
formatJavaScript :: String -> IO String
formatJavaScript jsCode = do
  -- Try npx prettier first
  tryPrettier "npx" ["prettier", "--parser", "babel"] jsCode
    `catch` (\(_ :: IOException) -> 
      -- Try global prettier
      tryPrettier "prettier" ["--parser", "babel"] jsCode
        `catch` (\(_ :: IOException) -> return jsCode))
  where
    tryPrettier cmd args input = do
      (exitCode, stdout, stderr) <- readProcessWithExitCode cmd args input
      case exitCode of
        ExitSuccess -> return stdout
        _ -> return input

-- | Process a Bend file and compile to JavaScript
processFileToJS :: FilePath -> IO ()
processFileToJS file = do
  book <- parseFile file
  let jsCode = JS.compile book
  formattedJS <- formatJavaScript jsCode
  putStrLn formattedJS



processFileToHVMT :: FilePath -> IO ()
processFileToHVMT file = do
  book <- parseFile file
  putStrLn (HVM.compile book)

processFileToHVMRun :: FilePath -> IO ()
processFileToHVMRun file = do
  book <- parseFile file
  let hvmOutput = HVM.compile book
  homedir <- getHomeDirectory
  let outputDir = homedir ++ "/.bend"
  let outputFile = trace ("outputDir:"++outputDir) (outputDir ++ "/out.hvm")
  createDirectoryIfMissing True outputDir
  writeFile outputFile hvmOutput
  (res,stats) <- runHVM outputFile (HVM.Ref "main" 0 []) HVM.API.Normalize
  putStrLn $ unlines $ map show res
  
-- | Process a Bend file and compile to HVM
processFileToHVM :: FilePath -> IO ()
processFileToHVM file = do
  book <- parseFile file
  let hvmCode = HVM.compile book
  putStrLn hvmCode


-- | List all dependencies of a Bend file (including transitive dependencies)
listDependencies :: FilePath -> IO ()
listDependencies file = do
  -- Parse and auto-import the file
  book <- parseFile file
  -- Collect all refs from the fully imported book
  let allRefs = collectAllRefs book
  -- Print all refs (these are all the dependencies)
  mapM_ putStrLn (S.toList allRefs)

-- | Collect all refs from a Book
collectAllRefs :: Book -> S.Set Name
collectAllRefs (Book defs) = 
  S.unions $ map collectRefsFromDefn (M.elems defs)
  where
    collectRefsFromDefn (_, term, typ) = S.union (getDeps term) (getDeps typ)
