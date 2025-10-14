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

import Control.Monad (unless, when)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Char (isAlphaNum, isSpace)
import Data.List (foldl', isPrefixOf, isSuffixOf, sortOn)
import Data.Maybe (fromJust, mapMaybe)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))
import Control.Exception (catch, IOException, throwIO, try)
import System.IO (hClose, hFlush, hPutStr, hPutStrLn, stderr, stdout)
import System.IO.Temp (withSystemTempFile)
import System.Timeout (timeout)
import Data.Typeable (Typeable, cast)

import Core.Adjust.Adjust (adjustBook, adjustBookWithPats)
import Core.Bind
import Core.Check
import Core.Deps
import Core.Import (autoImportWithExplicit, extractModuleName)
import Core.Parse.Book (doParseBook)
import Core.Parse.Parse (ParserState(..))
import Core.Type
import Core.Show (showTerm, BendException(..))
import Core.WHNF

import qualified Target.JavaScript as JS
import qualified Target.HVM as HVM
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
    Left err -> showErrAndDie err
    Right (book, parserState) -> do
      -- Auto-import unbound references with explicit import information
      autoImportedBook <- autoImportWithExplicit file book parserState
      return autoImportedBook
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
      generatedDefs <- generateDefinitions file bookForHVM mainFQN genInfos
      updatedContent <- applyGenerated content genInfos generatedDefs
      writeFile file updatedContent
      processFileInternal file False

data GenInfo = GenInfo
  { giSimpleName :: String
  , giSpan       :: Span
  }

parseBookWithAuto :: FilePath -> String -> IO (Book, Book)
parseBookWithAuto file content =
  case doParseBook file content of
    Left err -> showErrAndDie err
    Right (book, parserState) -> do
      autoImportedBook <- autoImportWithExplicit file book parserState
      return (book, autoImportedBook)

collectGenInfos :: FilePath -> Book -> [GenInfo]
collectGenInfos file (Book defs names) =
  mapMaybe lookupGen names
  where
    lookupGen name = do
      ( _inj, term, _typ) <- M.lookup name defs
      case term of
        Loc sp inner
          | spanPth sp == file
          , Met _ _ _ <- stripLoc inner ->
              let simple = extractSimpleName name
              in Just (GenInfo simple sp)
        _ -> Nothing
    stripLoc t = case t of
      Loc _ inner -> stripLoc inner
      other       -> other

extractSimpleName :: Name -> String
extractSimpleName name =
  case reverse (splitOnSep "::" name) of
    (simple:_) -> simple
    []         -> name

splitOnSep :: String -> String -> [String]
splitOnSep sep str = go str
  where
    go [] = [""]
    go s =
      case breakOnSep s of
        (chunk, Nothing)    -> [chunk]
        (chunk, Just rest') -> chunk : go rest'
    breakOnSep s =
      if sep `isPrefixOf` s
        then ("", Just (drop (length sep) s))
        else case s of
               []     -> ("", Nothing)
               (c:cs) ->
                 let (chunk, rest) = breakOnSep cs
                 in (c:chunk, rest)

bookHasMet :: Book -> Bool
bookHasMet (Book defs _) = any (\(_, term, _) -> termHasMet term) (M.elems defs)

generateDefinitions :: FilePath -> Book -> Name -> [GenInfo] -> IO (M.Map String String)
generateDefinitions _file book mainFQN genInfos = do
  let hvmCode = HVM.compile book mainFQN
  withSystemTempFile "bend-gen.hvm4" $ \tmpPath tmpHandle -> do
    hPutStr tmpHandle hvmCode
    hClose tmpHandle
    result <- timeout (5 * 1000000) (readProcessWithExitCode "hvm4" [tmpPath, "-C1", "-P"] "")
    case result of
      Nothing -> throwCliError "hvm4 timed out while generating code."
      Just (exitCode, stdoutStr, stderrStr) -> case exitCode of
        ExitSuccess -> do
          unless (null stderrStr) $
            throwCliError $ "hvm4 reported an error: " ++ stderrStr
          let parsed = parseGeneratedFunctions stdoutStr
          let missing = [giSimpleName info | info <- genInfos, M.notMember (giSimpleName info) parsed]
          unless (null missing) $
            throwCliError $ "hvm4 did not generate definitions for: " ++ show missing
          return parsed
        ExitFailure code ->
          throwCliError $ "hvm4 exited with code " ++ show code ++ ": " ++ stderrStr

applyGenerated :: String -> [GenInfo] -> M.Map String String -> IO String
applyGenerated content genInfos generated = do
  replacements <- mapM toReplacement genInfos
  case applySpanReplacements content replacements of
    Left err -> throwCliError err
    Right updated -> return updated
  where
    toReplacement info =
      case M.lookup (giSimpleName info) generated of
        Nothing     -> throwCliError $ "Missing generated definition for " ++ giSimpleName info
        Just result -> return (giSpan info, ensureTrailingNewline result)

ensureTrailingNewline :: String -> String
ensureTrailingNewline txt
  | null txt = txt
  | last txt == '\n' = txt
  | otherwise = txt ++ "\n"

applySpanReplacements :: String -> [(Span, String)] -> Either String String
applySpanReplacements original replacements = do
  converted <- mapM toOffsets replacements
  let sortedAsc = sortOn (\(s,_,_) -> s) converted
  unless (nonOverlapping sortedAsc) $
    Left "Generator definitions overlap; cannot rewrite file."
  let sortedDesc = sortOn (\(s,_,_) -> negate s) converted
  return $ foldl' applyOne original sortedDesc
  where
    toOffsets (sp, txt) = do
      let src = spanSrc sp
          reference = if null src then original else src
          start = positionToOffset reference (spanBeg sp)
          end   = positionToOffset reference (spanEnd sp)
      if start <= end && end <= length reference
        then Right (start, end, txt)
        else Left "Invalid span information for generator replacement."
    nonOverlapping [] = True
    nonOverlapping [_] = True
    nonOverlapping ((_,e1,_):(s2,e2,x2):rest) =
      e1 <= s2 && nonOverlapping ((s2,e2,x2):rest)
    applyOne acc (start, end, txt) =
      let (prefix, rest) = splitAt start acc
          (_, suffix) = splitAt (end - start) rest
      in prefix ++ txt ++ suffix

positionToOffset :: String -> (Int, Int) -> Int
positionToOffset src (line, col)
  | line <= 0 || col <= 0 = 0
  | otherwise =
      lineStartOffset src (line - 1) + (col - 1)

lineStartOffset :: String -> Int -> Int
lineStartOffset src linesToSkip = go src linesToSkip 0
  where
    go remaining 0 acc = acc
    go [] _ acc = acc
    go s n acc =
      let (before, after) = break (== '\n') s
          consumed = acc + length before
      in case after of
           []     -> consumed
           (_:rest) -> go rest (n - 1) (consumed + 1)

parseGeneratedFunctions :: String -> M.Map String String
parseGeneratedFunctions output = go (lines output) Nothing [] M.empty
  where
    go [] currentName currentLines acc =
      maybe acc (\name -> M.insert name (render currentLines) acc) currentName
    go (ln:rest) currentName currentLines acc =
      let trimmed = dropWhile isSpace ln
      in if "def " `isPrefixOf` trimmed
           then
             let acc' = maybe acc (\name -> M.insert name (render currentLines) acc) currentName
                 name = takeWhile isDefChar (drop 4 trimmed)
             in go rest (Just name) [ln] acc'
           else
             case currentName of
               Nothing -> go rest currentName currentLines acc
               Just _  -> go rest currentName (currentLines ++ [ln]) acc
    render ls = case ls of
      [] -> ""
      _  -> unlines ls
    isDefChar c = isAlphaNum c || c == '_' || c == '\''

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
  bookAdj@(Book defs names) <- case adjustBook book of
    Done b -> return b
    Fail e -> showErrAndDie e
  
  -- Find all generator definitions (contain a Met)
  let genDefs = M.filter (\(_, term, _) -> hasMet term) defs
  let genNames = M.keysSet genDefs

  -- Find all reverse dependencies (examples)
  let allDefs = M.toList defs
  let reverseDeps = S.fromList [ name | (name, (_, term, typ)) <- allDefs, not (name `S.member` genNames), not (S.null (S.intersection genNames (S.union (getDeps term) (getDeps typ)))) ]

  -- Get all dependencies of the generator definitions and the reverse dependencies
  let targetDefs = M.filterWithKey (\k _ -> k `S.member` genNames || k `S.member` reverseDeps) defs
  let allDeps = S.unions $ map (\(_, term, typ) -> S.union (getDeps term) (getDeps typ)) (M.elems targetDefs)

  -- Also include the names of the generator defs and reverse deps themselves
  let allNames = S.union genNames reverseDeps
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

showErrAndDie :: (Show a, Typeable a) => a -> IO b
showErrAndDie err = do
  case cast err of
    Just (msg :: String) -> hPutStrLn stderr msg
    Nothing -> hPutStrLn stderr (show err)
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
