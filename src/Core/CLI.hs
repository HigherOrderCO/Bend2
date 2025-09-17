module Core.CLI 
  ( parseFile
  , runMain
  , processFile
  , processFileToCore
  , processFileToJS
  , processFileToHVM
  , processFileToHS
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
import Control.Exception (catch, IOException, try)
import System.IO (hPutStrLn, stderr)

import Core.Adjust.Adjust (adjustBook, adjustBookWithPats)
import Core.Bind
import Core.Check
import Core.Deps
import Core.Import (autoImport, autoImportWithExplicit)
import Core.Parse.Book (doParseBook)
import Core.Parse.Parse (ParserState(..))
import Core.Type
import Core.Show (showTerm, BendException(..))
import Core.WHNF

import qualified Target.JavaScript as JS
import qualified Target.HVM as HVM
import qualified Target.Haskell as HS

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
    Right (book, parserState) -> do
      -- Auto-import unbound references with explicit import information
      autoImportedBook <- autoImportWithExplicit file book parserState
      return autoImportedBook
  where
    takeDirectory path = reverse . dropWhile (/= '/') . reverse $ path

-- | Run the main function from a book
runMain :: FilePath -> Book -> IO ()
runMain filePath book = do
  -- Extract module name from file path (same logic as takeBaseName')
  let moduleName = takeBaseName' filePath
      mainFQN = moduleName ++ "::main"
  case getDefn book mainFQN of
    Nothing -> do
      return ()
    Just _ -> do
      let mainCall = Ref mainFQN 1
      case infer 0 noSpan book (Ctx []) mainCall of
        Fail e -> do
          hPutStrLn stderr $ show e
          exitFailure
        Done typ -> do
          putStrLn ""
          print $ normal book mainCall
  where
    -- Helper function to extract module name from filepath (mirrors Import.hs logic)
    takeBaseName' :: FilePath -> String
    takeBaseName' path = 
      let withoutBend = if ".bend" `isSuffixOf'` path
                        then take (length path - 5) path  -- Remove .bend extension
                        else path
          -- Also remove /_ suffix if present (for files like Term/_.bend)
          withoutUnderscore = if "/_" `isSuffixOf'` withoutBend
                              then take (length withoutBend - 2) withoutBend  -- Remove /_
                              else withoutBend
      in withoutUnderscore
      where
        isSuffixOf' :: Eq a => [a] -> [a] -> Bool
        isSuffixOf' suffix str = suffix == drop (length str - length suffix) str

-- | Process a Bend file: parse, check, and run
processFile :: FilePath -> IO ()
processFile file = do
  book <- parseFile file
  result <- try $ do
    bookAdj <- case adjustBook book of
      Done b -> return b
      Fail e -> do
        hPutStrLn stderr $ show e
        exitFailure
    bookChk <- checkBook bookAdj
    runMain file bookChk
  case result of
    Left (BendException e) -> do
      hPutStrLn stderr $ show e
      exitFailure
    Right () -> return ()

-- | Process a Bend file and return it's Core form
processFileToCore :: FilePath -> IO ()
processFileToCore file = do
  book <- parseFile file
  result <- try $ do
    bookAdj <- case adjustBook book of
      Done b -> return b
      Fail e -> do
        hPutStrLn stderr $ show e
        exitFailure
    bookChk <- checkBook bookAdj
    putStrLn $ showBookWithFQN bookChk
  case result of
    Left (BendException e) -> do
      hPutStrLn stderr $ show e
      exitFailure
    Right () -> return ()
  where
    showBookWithFQN (Book defs names) = unlines [showDefn name (defs M.! name) | name <- names]
    showDefn k (_, x, t) = k ++ " : " ++ showTerm True False t ++ " = " ++ showTerm True False x

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
  result <- try $ do
    bookAdj <- case adjustBook book of
      Done b -> return b
      Fail e -> do
        hPutStrLn stderr $ show e
        exitFailure
    bookChk <- checkBook bookAdj
    let jsCode = JS.compile bookChk
    formattedJS <- formatJavaScript jsCode
    putStrLn formattedJS
  case result of
    Left (BendException e) -> do
      hPutStrLn stderr $ show e
      exitFailure
    Right () -> return ()

-- | Process a Bend file and compile to HVM
processFileToHVM :: FilePath -> IO ()
processFileToHVM file = do
  book <- parseFile file
  result <- try $ do
    bookAdj <- case adjustBookWithPats book of
      Done b -> return b
      Fail e -> do
        hPutStrLn stderr $ show e
        exitFailure
    -- putStrLn $ show bookAdj
    let hvmCode = HVM.compile bookAdj
    putStrLn hvmCode
  case result of
    Left (BendException e) -> do
      hPutStrLn stderr $ show e
      exitFailure
    Right () -> return ()

-- | Process a Bend file and compile to Haskell
processFileToHS :: FilePath -> IO ()
processFileToHS file = do
  book <- parseFile file
  result <- try $ do
    bookAdj <- case adjustBook book of
      Done b -> return b
      Fail e -> do
        hPutStrLn stderr $ show e
        exitFailure
    -- bookChk <- checkBook bookAdj
    -- putStrLn $ show bookChk
    let hsCode = HS.compile bookAdj
    putStrLn hsCode
  case result of
    Left (BendException e) -> do
      hPutStrLn stderr $ show e
      exitFailure
    Right () -> return ()

-- | List all dependencies of a Bend file (including transitive dependencies)
listDependencies :: FilePath -> IO ()
listDependencies file = do
  -- Parse and auto-import the file
  book <- parseFile file
  bookAdj <- case adjustBook book of
    Done b -> return b
    Fail e -> do
      hPutStrLn stderr $ show e
      exitFailure
  -- Collect all refs from the fully imported book
  let allRefs = collectAllRefs bookAdj
  -- Print all refs (these are all the dependencies)
  mapM_ putStrLn (S.toList allRefs)

-- | Get all dependencies needed for one or more Met statements.
getGenDeps :: FilePath -> IO ()
getGenDeps file = do
  book <- parseFile file
  bookAdj@(Book defs names) <- case adjustBook book of
    Done b -> return b
    Fail e -> do
      hPutStrLn stderr $ show e
      exitFailure
  
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
