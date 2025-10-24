module Core.CLI
  ( runCLI
  , CLIMode(..)
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
  ( bookHasMet
  , buildGenDepsBook
  , fillBook
  )
import Core.Adjust.Adjust (adjustBook, adjustBookWithPats)
import Core.Adjust.SplitAnnotate (check, infer)
import Core.Bind
import Core.Deps
import Core.Import (autoImportWithExplicit, extractModuleName, extractMainFQN)
import Core.Parse.Book (doParseBook)
import Core.Parse.Parse (ParserState(..))
import Core.Type
import Core.Show (showTerm, BendException(..))
import Core.WHNF

import qualified Target.JavaScript as JS
import qualified Target.HVM.HVM as HVM
import qualified Target.Haskell as HS

data CLIMode
  = CLI_RUN 
  | CLI_GEN_RUN 
  | CLI_SHOW_CORE
  | CLI_TO_JAVASCRIPT
  | CLI_TO_HVM
  | CLI_TO_HASKELL
  | CLI_LIST_DEPENDENCIES
  | CLI_GET_GEN_DEPS
  deriving Eq

runCLI :: FilePath -> CLIMode -> IO ()
runCLI path mode = do
  let allowGen  = mode `elem` [CLI_RUN]
      needCheck = mode `elem` [CLI_RUN, CLI_GEN_RUN, CLI_TO_JAVASCRIPT, CLI_SHOW_CORE]
  result <- try @BendException (runCLIGo path mode allowGen needCheck)
  case result of
    Left (BendException err) -> showErrAndDie err
    Right ()                 -> pure ()

runCLIGo :: FilePath -> CLIMode -> Bool -> Bool -> IO ()
runCLIGo path mode allowGen needCheck = do
  content <- readFile path
  (rawBook, importedBook) <- case doParseBook path content of
    Left err                  -> showErrAndDie err
    Right (book, parserState) -> do
      impBook <- autoImportWithExplicit path book parserState
      return (book, impBook)
  adjustedBook <- case adjustBook importedBook of
    Done b -> return b
    Fail e -> showErrAndDie e
  checkedBook  <- case needCheck of
    True  -> checkBook adjustedBook
    False -> pure adjustedBook 

  let mainFQN = extractMainFQN path checkedBook

  case mode of
    CLI_GEN_RUN ->
      if bookHasMet adjustedBook
      then do
        filledBookTxt <- fillBook path mainFQN content rawBook adjustedBook
        case filledBookTxt of
          Done txt -> writeFile path txt
          Fail e   -> showErrAndDie e
        runCLIGo path CLI_RUN False needCheck
      else runMain path checkedBook
    CLI_RUN ->
      if bookHasMet adjustedBook
      then showErrAndDie $ Unsupported noSpan (Ctx []) (Just  "Meta variables remain after generation; generation already attempted.")
      else runMain path checkedBook
    CLI_SHOW_CORE -> do 
      putStrLn $ showBookWithFQN checkedBook
        where
          showBookWithFQN (Book defs names _) = unlines [showDefn name (defs M.! name) | name <- names]
          showDefn k (_, x, t) = k ++ " : " ++ showTerm emptyBook t ++ " = " ++ showTerm emptyBook x
    CLI_TO_JAVASCRIPT -> do
      let jsCode = JS.compile checkedBook
      formattedJS <- formatJavaScript jsCode
      putStrLn formattedJS
    CLI_TO_HVM -> do
      let hvmCode = HVM.compile adjustedBook mainFQN
      putStrLn hvmCode
    CLI_TO_HASKELL -> do
      let hsCode = HS.compile adjustedBook mainFQN
      putStrLn hsCode
    CLI_LIST_DEPENDENCIES -> do
      let allRefs = collectAllRefs adjustedBook
      mapM_ putStrLn (S.toList allRefs)
      where
        collectAllRefs (Book defs _ _) = 
          S.unions $ map collectRefsFromDefn (M.elems defs)
        collectRefsFromDefn (_, term, typ) = S.union (getDeps term) (getDeps typ)
    CLI_GET_GEN_DEPS -> do
      print $ buildGenDepsBook adjustedBook

checkBook :: Book -> IO Book
checkBook book@(Book defs names m) = do
  let orderedDefs = [(name, fromJust (M.lookup name defs)) | name <- names]
  (annotatedDefs, success) <- foldM checkAndAccumulate ([], True) orderedDefs
  unless success exitFailure
  return $ Book (M.fromList (reverse annotatedDefs)) names m
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

-- | Run the main function from a book
runMain :: FilePath -> Book -> IO ()
runMain filePath book = do
  let mainFQN = extractMainFQN filePath book
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

showErrAndDie :: (Show a, Typeable a) => a -> IO b
showErrAndDie err = do
  let rendered = case readMaybe (show err) :: Maybe String of
        Just txt -> txt
        Nothing  -> show err
  hPutStrLn stderr rendered
  exitFailure

-- IO Helper Functions
-- ===================

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
