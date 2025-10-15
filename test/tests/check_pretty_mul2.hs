{-# LANGUAGE OverloadedStrings #-}

import Test (assert, findProjectRoot, has)

import Control.Exception (finally)
import System.Directory (createDirectory, doesDirectoryExist, getTemporaryDirectory, removeDirectoryRecursive)
import System.FilePath ((</>))
import System.Process (proc, readCreateProcessWithExitCode, CreateProcess(..))
import System.Exit (ExitCode(..))

main :: IO ()
main = withTempDirectory "bend-pretty-test" $ \tmpDir -> do
  let bendRoot = tmpDir </> "BendRoot"
      bendFile = bendRoot </> "main.bend"
  createDirectory bendRoot
  writeFile bendFile generatorSource

  projectDir <- findProjectRoot
  let cmd = (proc "cabal"
                [ "run"
                , "-v0"
                , "bend"
                , "--project-dir=" ++ projectDir
                , "--"
                , "main.bend"
                ]) { cwd = Just bendRoot }
  (exitCode, out, err) <- readCreateProcessWithExitCode cmd ""

  assert (exitCode == ExitSuccess)
  assert (null err)
  -- bend prints progress with ANSI colors; just ensure we saw success marker
  assert (out `has` "✓ main::mul2")

  final <- readFile bendFile
  assert (final == expectedOutput)

generatorSource :: String
generatorSource = unlines
  [ "gen mul2(n: Nat) -> Nat"
  , ""
  , "assert mul2(2n) == 4n : Nat"
  , "assert mul2(0n) == 0n : Nat"
  , "assert mul2(3n) == 6n : Nat"
  ]

expectedOutput :: String
expectedOutput = unlines
  [ "def mul2(n: Nat) -> Nat:"
  , "  match n:"
  , "    case 0n:"
  , "      return 0n"
  , "    case 1n+p:"
  , "      return 2n+mul2(p)"
  , ""
  , ""
  , "assert mul2(2n) == 4n : Nat"
  , "assert mul2(0n) == 0n : Nat"
  , "assert mul2(3n) == 6n : Nat"
  ]

withTempDirectory :: String -> (FilePath -> IO a) -> IO a
withTempDirectory prefix action = do
  base <- getTemporaryDirectory
  let go (n :: Int) = do
        let dir = base </> (prefix ++ "-" ++ show n)
        exists <- doesDirectoryExist dir
        if exists
          then go (n + 1)
          else do
            createDirectory dir
            action dir `finally` removeDirectoryRecursive dir
  go 0
