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
import System.IO (hPutStrLn, stderr, hFlush, stdout)

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
      putStrLn $ show book
      -- Auto-import unbound references with explicit import information
      autoImportedBook <- autoImportWithExplicit file book parserState
      return autoImportedBook
  where
    takeDirectory path = reverse . dropWhile (/= '/') . reverse $ path

-- | Execute a normalized IO action and return the result
executeIOWithResult :: Book -> Term -> IO Term
executeIOWithResult book ioAction = case ioAction of
  -- IO_PURE just returns a value (no side effect)
  App (Pri IO_PURE) val -> return val

  -- IO_PUTC outputs a character and returns Unit
  App (Pri IO_PUTC) chr -> do
    case chr of
      Val (CHR_V c) -> do
        putChar c
        hFlush stdout
      Val (U64_V n) -> do
        putChar (toEnum (fromIntegral n) :: Char)
        hFlush stdout
      Val (I64_V n) -> do
        putChar (toEnum (fromIntegral n) :: Char)
        hFlush stdout
      _ -> return ()
    return Uni

  -- IO_PRINT outputs a string and returns Unit
  App (Pri IO_PRINT) str -> do
    let chars = extractString book str
    putStr chars
    hFlush stdout
    return Uni

  -- IO_GETC reads a character and returns it
  Pri IO_GETC -> do
    c <- getChar
    return (Val (CHR_V c))

  -- IO_READ_FILE reads a file and returns its contents as a string
  App (Pri IO_READ_FILE) path -> do
    let pathStr = extractString book path
    contents <- readFile pathStr
    return (stringToTerm contents)

  -- IO_WRITE_FILE writes to a file and returns Unit
  App (App (Pri IO_WRITE_FILE) path) content -> do
    let pathStr = extractString book path
    let contentStr = extractString book content
    writeFile pathStr contentStr
    return Uni

  -- IO_BIND sequences two IO actions (with type parameters)
  -- Pattern: IO_BIND<A, B>(action, cont)
  App (App (App (App (Pri IO_BIND) _typeA) _typeB) action) cont -> do
    -- Execute the first action and get its result
    result <- executeIOWithResult book action
    -- Apply the continuation to the result
    let nextAction = normal book (App cont result)
    executeIOWithResult book nextAction

  -- IO_BIND without type parameters (backwards compatibility)
  App (App (Pri IO_BIND) action) cont -> do
    -- Execute the first action and get its result
    result <- executeIOWithResult book action
    -- Apply the continuation to the result
    let nextAction = normal book (App cont result)
    executeIOWithResult book nextAction

  _ -> return Uni  -- Unknown IO action, return Unit

-- | Execute a normalized IO action (wrapper that discards result)
executeIO :: Book -> Term -> IO ()
executeIO book ioAction = do
  _ <- executeIOWithResult book ioAction
  return ()

-- | Convert a Haskell String to a Bend term (character list)
stringToTerm :: String -> Term
stringToTerm [] = Nil
stringToTerm (c:cs) = Con (Val (CHR_V c)) (stringToTerm cs)

-- | Extract a Haskell String from a Bend string (Lst (Num CHR_T))
extractString :: Book -> Term -> String
extractString book term = case normal book term of
  Nil -> ""
  Con chr tail -> case chr of
    Val (CHR_V c) -> c : extractString book tail
    Val (U64_V n) -> (toEnum (fromIntegral n) :: Char) : extractString book tail
    Val (I64_V n) -> (toEnum (fromIntegral n) :: Char) : extractString book tail
    _ -> extractString book tail  -- Skip non-character values
  _ -> ""

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
          -- Normalize the type to check if it's IO
          let normTyp = normal book typ
          case normTyp of
            IO _ -> do
              -- For IO types, normalize and execute the IO action
              let normalizedIO = normal book mainCall
              executeIO book normalizedIO
            _ -> do
              -- For non-IO types, just print the normalized result
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
