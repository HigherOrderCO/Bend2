module Test where

import System.Process
import System.Directory
import System.FilePath
import System.Exit
import Control.Exception (try, throwIO, finally, evaluate)
import Control.Monad (when)
import Data.List (isInfixOf, isPrefixOf)
import Data.Char (isSpace)
import System.Timeout (timeout)
import System.IO (hClose, hGetContents)

test :: String -> [(String, String)] -> String -> (String -> String -> IO ()) -> IO ()
test cmd files desc callback = testWithTimeout cmd files desc callback (30 * 1000000) -- 30 seconds default

testWithTimeout :: String -> [(String, String)] -> String -> (String -> String -> IO ()) -> Int -> IO ()
testWithTimeout cmd files desc callback timeoutMicros = do
  -- Print description if not empty
  when (not $ null desc) $ putStrLn $ "  \ESC[2m" ++ desc ++ "\ESC[0m"  -- dim/gray
  tmpDir <- getTemporaryDirectory
  testDir <- findUniqueTestDir tmpDir (0 :: Int)
  createDirectory testDir
  let (useBendRoot, actualCmd) = case cmd of
        ('!':rest) -> (False, dropWhile (== ' ') rest)
        _          -> (True, cmd)
  -- Capture the test result first
  (out, err) <- finally (runTest testDir useBendRoot actualCmd) (removeDirectoryRecursive testDir)

  -- Run the callback and check if test passes
  testPassed <- try (callback out err) :: IO (Either ExitCode ())
  let success = case testPassed of
                  Right _ -> True
                  Left _  -> False

  -- Print the bend output with appropriate color
  let output = out ++ err
  let outputLines = lines output
  let color = if success then "\ESC[32m" else "\ESC[31m"
  let resetColor = "\ESC[0m"
  mapM_ (\line -> putStrLn $ "  " ++ color ++ ">" ++ resetColor ++ " " ++ line) outputLines

  -- Re-throw if test failed
  case testPassed of
    Left e  -> throwIO e
    Right _ -> return ()

  where
    findUniqueTestDir base n = do
      let dir = base </> ("bend-test-" ++ show n)
      exists <- doesDirectoryExist dir
      if exists then findUniqueTestDir base (n + 1) else return dir

    -- Corrected runTest function
    runTest testDir useBendRoot actualCmd = do
      when useBendRoot $ createDirectoryIfMissing True (testDir </> "BendRoot")
      mapM_ (writeTestFile testDir useBendRoot) files

      -- Find project directory by looking for bend.cabal
      projectDir <- findProjectRoot
      
      let cmdWords = words actualCmd
      let fullCmd = case cmdWords of
                      ("bend":args) -> "cabal run -v0 bend --project-dir=" ++ projectDir ++ " -- " ++ unwords args
                      _             -> actualCmd

      -- Create the process in its own group to kill it and its children
      let workingDir = if useBendRoot then testDir </> "BendRoot" else testDir
      let procSpec = (shell $ "cd " ++ workingDir ++ " && " ++ fullCmd)
            { std_out = CreatePipe
            , std_err = CreatePipe
            , create_group = True -- IMPORTANT: For POSIX systems (Linux/macOS)
            }

      withCreateProcess procSpec $ \_ (Just stdout_h) (Just stderr_h) ph -> do
        -- Use timeout on waiting for the process to complete
        result <- timeout timeoutMicros (waitForProcess ph)

        case result of
          Just _ -> do
            -- Process finished normally, grab output
            out <- hGetContents stdout_h
            err <- hGetContents stderr_h
            -- Fully evaluate the output strings before the handles are closed
            _ <- evaluate (length out + length err)
            return (out, err)
          Nothing -> do
            -- Process timed out. Terminate the entire process group.
            interruptProcessGroupOf ph
            -- Wait for the process to truly die to avoid zombies
            _ <- waitForProcess ph
            return ("", "ERROR: Test timed out after " ++ show (timeoutMicros `div` 1000000) ++ " seconds")

    writeTestFile testDir useBendRoot (name, content) = do
      let relative =
            if useBendRoot
              then if "BendRoot/" `isPrefixOf` name
                     then name
                     else "BendRoot/" ++ name
              else name
      let path = testDir </> relative
      createDirectoryIfMissing True (takeDirectory path)
      writeFile path content

testFile :: String -> String -> (String -> String -> IO ()) -> IO ()
testFile code desc callback = test "bend main.bend" [("main.bend", code)] desc callback

testFileWithTimeout :: String -> String -> (String -> String -> IO ()) -> Int -> IO ()
testFileWithTimeout code desc callback timeoutSeconds = testWithTimeout "bend main.bend" [("main.bend", code)] desc callback (timeoutSeconds * 1000000)

-- Alias for tests that just check if a file type-checks (err == "")
testFileChecks :: String -> IO ()
testFileChecks code = testFile code "must check" $ \out err -> do
  assert (err == "")

-- Test that a file produces a specific goal in the error output
-- Also checks that specific variables have specific types in the context
testFileGoal :: String -> String -> [(String, String)] -> IO ()
testFileGoal code expectedGoal contextChecks =
  testFile code ("must show goal: " ++ expectedGoal) $ \out err -> do
    -- Check that we have a mismatch error (not empty err)
    assert (err /= "")
    -- Check that it's a mismatch error
    assert (err `has` "Mismatch:")
    -- Check that the goal matches
    assert (err `has` ("Goal: " ++ expectedGoal))
    -- Check context variables
    mapM_ (\(varName, varType) -> assert (err `has` ("- " ++ varName ++ " : " ++ varType))) contextChecks

assert :: Bool -> IO ()
assert True  = return ()
assert False = exitFailure

-- Internal helper to strip ANSI colors
stripAnsiColors :: String -> String
stripAnsiColors = stripAnsi
  where
    stripAnsi [] = []
    stripAnsi ('\ESC':'[':xs) = stripAnsi (dropWhile (/= 'm') xs)
    stripAnsi (x:xs) = x : stripAnsi xs

-- Find the project root by looking for bend.cabal
findProjectRoot :: IO FilePath
findProjectRoot = do
  cwd <- getCurrentDirectory
  searchUpwards cwd
  where
    searchUpwards :: FilePath -> IO FilePath
    searchUpwards dir = do
      let cabalFile = dir </> "bend.cabal"
      exists <- doesFileExist cabalFile
      if exists
        then return dir
        else do
          let parent = takeDirectory dir
          if parent == dir  -- reached root
            then error "Could not find bend.cabal in any parent directory"
            else searchUpwards parent

-- Infix operator to check if output contains expected text
-- Automatically handles ANSI colors and normalizes whitespace
has :: String -> String -> Bool
output `has` expected =
  let cleanExpected = filter (not . isSpace) expected
      cleanOutput = filter (not . isSpace) (stripAnsiColors output)
  in cleanExpected `isInfixOf` cleanOutput
