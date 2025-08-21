module Core.CLI 
  ( parseFile
  , runMain
  , processFile
  , processFileToJS
  , processFileToHVM
  , listDependencies
  , getGenDeps
  ) where

import Control.Monad (unless, forM_)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromJust)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))
import Control.Exception (catch, IOException)
import System.IO (hPutStrLn, stderr)

import Core.Adjust.Adjust (adjustBook, adjustBookWithPats)
import Core.Bind
import Core.Check
import Core.Deps
import Core.Import (autoImport)
import Core.Parse.Book (doParseBook)
import Core.Type
import Core.Show
import Core.WHNF
-- debug import removed

import qualified Target.JavaScript as JS
import qualified Target.HVM as HVM

-- Type-check all definitions in a book
checkBook :: Book -> IO Book
checkBook book@(Book defs names) = do
  let orderedDefs = [(name, fromJust (M.lookup name defs)) | name <- names]
  success <- checkAll book orderedDefs
  unless success exitFailure
  return book
  where
    checkDef bk term typ = do
      check 0 noSpan bk (Ctx []) typ Set
      check 0 noSpan bk (Ctx []) term typ
      return ()
    checkAll :: Book -> [(Name, Defn)] -> IO Bool
    checkAll bk [] = return True
    checkAll bk ((name, (inj, term, typ)):rest) = do
      case checkDef bk term typ of
        Done () -> do
          putStrLn $ "\x1b[32m✓ " ++ name ++ "\x1b[0m"
          checkAll bk rest
        Fail e -> do
          hPutStrLn stderr $ "\x1b[31m✗ " ++ name ++ "\x1b[0m"
          hPutStrLn stderr $ show e
          success <- checkAll bk rest
          return False

-- | Parse a Bend file into a Book
parseFile :: FilePath -> IO Book
parseFile file = do
  content <- readFile file
  case doParseBook file content of
    Left err -> do
      hPutStrLn stderr $ err
      exitFailure
    Right book -> do
      -- Auto-import unbound references
      autoImportedBook <- autoImport (takeDirectory file) book
      return autoImportedBook
  where
    takeDirectory path = reverse . dropWhile (/= '/') . reverse $ path

-- | Run the main function from a book
runMain :: Book -> IO ()
runMain book = do
  case getDefn book "main" of
    Nothing -> do
      return ()
    Just _ -> do
      let mainCall = Ref "main" 1
      case infer 0 noSpan book (Ctx []) mainCall of
        Fail e -> do
          hPutStrLn stderr $ show e
          exitFailure
        Done typ -> do
          putStrLn ""
          print $ normal book mainCall

-- | Process a Bend file: parse, check, and run
processFile :: FilePath -> IO ()
processFile file = do
  book <- parseFile file
  let bookAdj = adjustBook book
  -- debug removed
  -- debug removed
  bookChk <- checkBook bookAdj
  runMain bookChk

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
  let bookAdj = adjustBook book
  bookChk <- checkBook bookAdj
  let jsCode = JS.compile bookChk
  formattedJS <- formatJavaScript jsCode
  putStrLn formattedJS

-- | Process a Bend file and compile to HVM
processFileToHVM :: FilePath -> IO ()
processFileToHVM file = do
  book <- parseFile file
  let bookAdj = adjustBookWithPats book
  -- putStrLn $ show bookAdj
  let hvmCode = HVM.compile bookAdj
  putStrLn hvmCode

-- | List all dependencies of a Bend file (including transitive dependencies)
listDependencies :: FilePath -> IO ()
listDependencies file = do
  -- Parse and auto-import the file
  book <- parseFile file
  let bookAdj = adjustBook book
  -- Collect all refs from the fully imported book
  let allRefs = collectAllRefs bookAdj
  -- Print all refs (these are all the dependencies)
  mapM_ putStrLn (S.toList allRefs)

-- | Get all dependencies needed for one or more Met statements.
getGenDeps :: FilePath -> IO ()
getGenDeps file = do
  book <- parseFile file
  let bookAdj@(Book defs names) = adjustBook book
  
  -- Find all definitions that are `try` definitions (i.e., contain a Met)
  let tryDefs = M.filter (\(_, term, _) -> hasMet term) defs
  let tryNames = M.keysSet tryDefs

  -- Find all reverse dependencies (examples)
  let allDefs = M.toList defs
  let reverseDeps = S.fromList [ name | (name, (_, term, typ)) <- allDefs, not (name `S.member` tryNames), not (S.null (S.intersection tryNames (S.union (getDeps term) (getDeps typ)))) ]

  -- Get all dependencies of the `try` definitions and the reverse dependencies
  let targetDefs = M.filterWithKey (\k _ -> k `S.member` tryNames || k `S.member` reverseDeps) defs
  let allDeps = S.unions $ map (\(_, term, typ) -> S.union (getDeps term) (getDeps typ)) (M.elems targetDefs)

  -- Also include the names of the try defs and reverse deps themselves
  let allNames = S.union tryNames reverseDeps
  let finalDepNames = S.union allNames allDeps

  -- Filter the book to get the definitions we want to print
  let finalDefs = M.filterWithKey (\k _ -> k `S.member` finalDepNames) defs
  let finalNames = filter (`S.member` finalDepNames) names
  
  -- Print the resulting book
  print $ Book finalDefs finalNames

-- | Collect all refs from a Book
collectAllRefs :: Book -> S.Set Name
collectAllRefs (Book defs _) = 
  S.unions $ map collectRefsFromDefn (M.elems defs)
  where
    collectRefsFromDefn (_, term, typ) = S.union (getDeps term) (getDeps typ)

-- | Check if a term contains a Metavar
hasMet :: Term -> Bool
hasMet term = case term of
  Met {}      -> True
  Sub t       -> hasMet t
  Fix _ f     -> hasMet (f (Var "" 0))
  Let k t v f -> case t of
    Just t    -> hasMet t || hasMet v || hasMet (f (Var k 0))
    Nothing   -> hasMet v || hasMet (f (Var k 0))
  Use k v f   -> hasMet v || hasMet (f (Var k 0))
  Chk x t     -> hasMet x || hasMet t
  EmpM        -> False
  UniM f      -> hasMet f
  BitM f t    -> hasMet f || hasMet t
  Suc n       -> hasMet n
  NatM z s    -> hasMet z || hasMet s
  Lst t       -> hasMet t
  Con h t     -> hasMet h || hasMet t
  LstM n c    -> hasMet n || hasMet c
  EnuM cs e   -> any (hasMet . snd) cs || hasMet e
  Op2 _ a b   -> hasMet a || hasMet b
  Op1 _ a     -> hasMet a
  Sig a b     -> hasMet a || hasMet b
  Tup a b     -> hasMet a || hasMet b
  SigM f      -> hasMet f
  All a b     -> hasMet a || hasMet b
  Lam _ t f   -> maybe False hasMet t || hasMet (f (Var "" 0))
  App f x     -> hasMet f || hasMet x
  Eql t a b   -> hasMet t || hasMet a || hasMet b
  EqlM f      -> hasMet f
  Rwt e f     -> hasMet e || hasMet f
  Sup _ a b   -> hasMet a || hasMet b
  SupM l f    -> hasMet l || hasMet f
  Loc _ t     -> hasMet t
  Log s x     -> hasMet s || hasMet x
  Pat s m c   -> any hasMet s || any (hasMet . snd) m || any (\(p,b) -> any hasMet p || hasMet b) c
  Frk l a b   -> hasMet l || hasMet a || hasMet b
  _           -> False
