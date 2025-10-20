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

import Control.Monad (unless, when, forM_, foldM)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromJust)
import Debug.Trace
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))
import Control.Exception (catch, IOException, throwIO, try)
import System.IO (hFlush, hPutStr, hPutStrLn, stderr, stdout)
import Data.Typeable (Typeable)
import Text.Read (readMaybe)

import Core.Gen
  ( applyGenerated
  , bookHasMet
  , buildGenDepsBook
  , collectGenInfos
  , generateDefinitions
  )
import Core.Adjust.Adjust (adjustBook, adjustBookWithPats)
import Core.Adjust.SplitAnnotate (check, infer)
import Core.Bind
-- import Core.Check
import Core.Deps
-- import Core.Import (autoImportWithExplicit, extractModuleName)
import Core.Import (extractModuleName)
import Core.Parse.Book (doParseBook)
import Core.Parse.Parse (ParserState(..))
import Core.Type
import Core.Show (showTerm, BendException(..))
import Core.WHNF

import qualified Target.JavaScript as JS
import qualified Target.HVM.HVM as HVM
import qualified Target.Haskell as HS

-- IO Runtime
-- ==========

-- Execute an IO action term and return the result
executeIO :: Book -> Term -> IO Term
executeIO book action = case whnf book action of
    Pri IO_GETC -> do
      c <- getChar
      return (Val (CHR_V c))
    App (App (Pri IO_PURE) typ) v -> return v
    App (Pri IO_PRINT) s -> case termToString book s of
      Just str -> putStr str >> hFlush stdout >> return One
      Nothing -> return One
    App (Pri IO_PUTC) (Val (CHR_V c)) -> putChar c >> hFlush stdout >> return One
    App (Pri IO_PUTC) (Val (U64_V n)) -> putChar (toEnum (fromIntegral n)) >> hFlush stdout >> return One
    App (Pri IO_READ_FILE) path -> case termToString book path of
      Just filepath -> do
        contents <- readFile filepath
        return (stringToTerm contents)
      Nothing -> return Nil
    App (App (Pri IO_WRITE_FILE) path) content -> case termToString book path of
      Just filepath -> case termToString book content of
        Just str -> writeFile filepath str >> return One
        Nothing -> return One
      Nothing -> return One
    -- Handle IO_BIND by executing action then continuation
    App (App (App (App (Pri IO_BIND) _) _) action) cont -> do
      result <- executeIO book action
      executeIO book (whnf book (App cont result))
    _ -> return One

checkBook :: Book -> IO Book
checkBook book@(Book defs names) = do
  let orderedDefs = [(name, fromJust (M.lookup name defs)) | name <- names]
  (annotatedDefs, success) <- foldM checkAndAccumulate ([], True) orderedDefs
  unless success exitFailure
  return $ Book (M.fromList (reverse annotatedDefs)) names
  where
    checkAndAccumulate (accDefs, accSuccess) (name, (inj, term, typ)) = do
      let checkResult = do 
            typ'  <- check 0 noSpan book (Ctx []) typ Set
            term' <- check 0 noSpan book (Ctx []) term typ'
            -- traceM $ "-chec: " ++ show term'
            return (inj, term', typ')
      case checkResult of
        Done (inj', term', typ') -> do
          putStrLn $ "\x1b[32m✓ " ++ name ++ "\x1b[0m"
          return ((name, (inj', term', typ')) : accDefs, accSuccess)
        Fail e -> do
          hPutStrLn stderr $ "\x1b[31m✗ " ++ name ++ "\x1b[0m"
          hPutStrLn stderr $ show e
          -- Keep original term when check fails
          return ((name, (inj, term, typ)) : accDefs, False)

-- | Parse a Bend file into a Book
parseFile :: FilePath -> IO Book
parseFile file = do
  content <- readFile file
  case doParseBook file content of
    Left err -> showErrAndDie err
    Right (book, _parserState) -> do
      -- Auto-import unbound references with explicit import information
      -- autoImportedBook <- autoImportWithExplicit file book parserState
      -- return autoImportedBook
      return book
  where
    takeDirectory path = reverse . dropWhile (/= '/') . reverse $ path

-- | Run the main function from a book
runMain :: FilePath -> Book -> IO ()
runMain filePath book = do
  let moduleName = extractModuleName filePath
      mainFQN = moduleName ++ "::main"
  case getDefn book mainFQN of
    Nothing -> do
      return ()
    Just _ -> do
      let mainCall = Ref mainFQN 1
      case infer 0 noSpan book (Ctx []) mainCall of
        Fail e -> showErrAndDie e
        Done typ -> do
          -- Check if main has IO type and run it properly
          case whnf book typ of
            Core.Type.IO _ -> do
              result <- executeIO book mainCall
              -- Print the result if it's not Unit
              case result of
                One -> return ()  -- Unit type, don't print
                _ -> print $ normal book result
            _ -> print $ normal book mainCall

-- | Process a Bend file: parse, check, and run
processFile :: FilePath -> IO ()
processFile file = do
  result <- try $ processFileInternal file True
  case result of
    Left (BendException e) -> showErrAndDie e
    Right () -> return ()

processFileInternal :: FilePath -> Bool -> IO ()
processFileInternal file allowGeneration = do
  content <- readFile file
  (rawBook, importedBook) <- parseBookWithAuto file content
  let moduleName = extractModuleName file
      mainFQN = moduleName ++ "::main"
      genInfos = collectGenInfos file rawBook

  bookAdj <- case adjustBook importedBook of
    Done b -> return b
    Fail e -> showErrAndDie e
  let metasPresent = bookHasMet bookAdj
  bookChk <- checkBook bookAdj

  if null genInfos
    then do
      when metasPresent $
        throwCliError "Meta variables remain after generation; run `bend verify` for detailed errors."
      runMain file bookChk
    else do
      when (not allowGeneration) $
        throwCliError "Meta variables remain after generation; generation already attempted."
      bookForHVM <- case adjustBook importedBook of
        Done b -> return b
        Fail e -> showErrAndDie e
      generatedDefsResult <- generateDefinitions file bookForHVM mainFQN genInfos
      generatedDefs <- case generatedDefsResult of
        Left err   -> throwCliError err
        Right defs -> pure defs
      let updatedContentResult = applyGenerated content genInfos generatedDefs
      updatedContent <- case updatedContentResult of
        Left err      -> throwCliError err
        Right updated -> pure updated
      writeFile file updatedContent
      processFileInternal file False

parseBookWithAuto :: FilePath -> String -> IO (Book, Book)
parseBookWithAuto file content =
  case doParseBook file content of
    Left err -> showErrAndDie err
    Right (book, _parserState) -> do
      -- autoImportedBook <- autoImportWithExplicit file book parserState
      -- return (book, autoImportedBook)
      return (book, book)


throwCliError :: String -> IO a
throwCliError msg = throwIO (BendException $ Unsupported noSpan (Ctx []) (Just msg))

-- | Process a Bend file and return it's Core form
processFileToCore :: FilePath -> IO ()
processFileToCore file = do
  book <- parseFile file
  result <- try $ do
    bookAdj <- case adjustBook book of
      Done b -> return b
      Fail e -> showErrAndDie e
    bookChk <- checkBook bookAdj
    putStrLn $ showBookWithFQN bookChk
  case result of
    Left (BendException e) -> showErrAndDie e
    Right () -> return ()
  where
    showBookWithFQN (Book defs names) = unlines [showDefn name (defs M.! name) | name <- names]
    showDefn k (_, x, t) = k ++ " : " ++ showTerm True t ++ " = " ++ showTerm True x

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
      Fail e -> showErrAndDie e
    bookChk <- checkBook bookAdj
    let jsCode = JS.compile bookChk
    formattedJS <- formatJavaScript jsCode
    putStrLn formattedJS
  case result of
    Left (BendException e) -> showErrAndDie e
    Right () -> return ()

-- | Process a Bend file and compile to HVM
processFileToHVM :: FilePath -> IO ()
processFileToHVM file = do
  let moduleName = extractModuleName file
  let mainFQN = moduleName ++ "::main"
  book <- parseFile file
  result <- try $ do
    bookAdj <- case adjustBook book of
      Done b -> return b
      Fail e -> showErrAndDie e
    -- putStrLn $ show bookAdj
    let hvmCode = HVM.compile bookAdj mainFQN
    putStrLn hvmCode
  case result of
    Left (BendException e) -> showErrAndDie e
    Right () -> return ()

-- | Process a Bend file and compile to Haskell
processFileToHS :: FilePath -> IO ()
processFileToHS file = do
  let moduleName = extractModuleName file
  let mainFQN = moduleName ++ "::main"
  book <- parseFile file
  result <- try $ do
    bookAdj <- case adjustBook book of
      Done b -> return b
      Fail e -> showErrAndDie e
    -- bookChk <- checkBook bookAdj
    -- putStrLn $ show bookChk
    let hsCode = HS.compile bookAdj mainFQN
    putStrLn hsCode
  case result of
    Left (BendException e) -> showErrAndDie e
    Right () -> return ()

-- | List all dependencies of a Bend file (including transitive dependencies)
listDependencies :: FilePath -> IO ()
listDependencies file = do
  -- Parse and auto-import the file
  book <- parseFile file
  bookAdj <- case adjustBook book of
    Done b -> return b
    Fail e -> showErrAndDie e
  -- Collect all refs from the fully imported book
  let allRefs = collectAllRefs bookAdj
  -- Print all refs (these are all the dependencies)
  mapM_ putStrLn (S.toList allRefs)

-- | Get all dependencies needed for one or more Met statements.
getGenDeps :: FilePath -> IO ()
getGenDeps file = do
  book <- parseFile file
  bookAdj <- case adjustBook book of
    Done b -> return b
    Fail e -> showErrAndDie e
  print $ buildGenDepsBook bookAdj

-- | Collect all refs from a Book
collectAllRefs :: Book -> S.Set Name
collectAllRefs (Book defs _) = 
  S.unions $ map collectRefsFromDefn (M.elems defs)
  where
    collectRefsFromDefn (_, term, typ) = S.union (getDeps term) (getDeps typ)

showErrAndDie :: (Show a, Typeable a) => a -> IO b
showErrAndDie err = do
  let rendered = case readMaybe (show err) :: Maybe String of
        Just txt -> txt
        Nothing  -> show err
  hPutStrLn stderr rendered
  exitFailure

-- IO Helper Functions
-- ===================

-- Convert a Bend string (character list) to a Haskell String
termToString :: Book -> Term -> Maybe String
termToString book term = go (whnf book term)
  where
    go Nil = Just ""
    go (Con (Val (CHR_V c)) rest) = do
      restStr <- go (whnf book rest)
      return (c : restStr)
    go _ = Nothing

-- Convert a Haskell String to a Bend string (character list)
stringToTerm :: String -> Term
stringToTerm [] = Nil
stringToTerm (c:cs) = Con (Val (CHR_V c)) (stringToTerm cs)
