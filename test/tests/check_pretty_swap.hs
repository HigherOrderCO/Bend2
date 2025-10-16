{-# LANGUAGE OverloadedStrings #-}

import Test (assert, findProjectRoot, has)

import Control.Exception (finally)
import System.Directory (createDirectory, createDirectoryIfMissing, doesDirectoryExist, getEnvironment, getTemporaryDirectory, removeDirectoryRecursive)
import System.FilePath ((</>))
import System.Process (CreateProcess(..), proc, readCreateProcessWithExitCode)
import System.Exit (ExitCode(..))

main :: IO ()
main = withTempDirectory "bend-pretty-swap-test" $ \tmpDir -> do
  let bendRoot = tmpDir </> "BendRoot"
      bendFile = bendRoot </> "swap.bend"
  createDirectory bendRoot
  writeFile bendFile generatorSource

  projectDir <- findProjectRoot
  env0 <- getEnvironment
  let cabalDir = tmpDir </> "cabal-cache"
  createDirectoryIfMissing True cabalDir
  let envVars = ("CABAL_DIR", cabalDir) : filter ((/= "CABAL_DIR") . fst) env0
  let cmd = (proc "cabal"
                [ "run"
                , "-v0"
                , "bend"
                , "--project-dir=" ++ projectDir
                , "--"
                , "swap.bend"
                ]) { cwd = Just bendRoot
                    , env = Just envVars
                    }
  (exitCode, out, err) <- readCreateProcessWithExitCode cmd ""

  assert (exitCode == ExitSuccess)
  assert (null err)
  assert (out `has` "✓ swap::swap")

  final <- readFile bendFile
  assert (final == expectedOutput)

generatorSource :: String
generatorSource = unlines
  [ "gen swap(a: (Nat & Nat)) -> (Nat & Nat)"
  , ""
  , "assert swap((1n, 2n)) == (2n, 1n) : Nat & Nat"
  , "assert swap((0n, 5n)) == (5n, 0n) : Nat & Nat"
  , "assert swap((0n, 0n)) == (0n, 0n) : Nat & Nat"
  , ""
  , "def main() -> Nat & Nat:"
  , "  swap((3n, 0n))"
  ]

expectedOutput :: String
expectedOutput = unlines
  [ "def swap(a: (Nat & Nat)) -> (Nat & Nat):"
  , "  match a:"
  , "    case (a1, b):"
  , "      return (b, a1)"
  , ""
  , ""
  , ""
  , "assert swap((1n, 2n)) == (2n, 1n) : Nat & Nat"
  , "assert swap((0n, 5n)) == (5n, 0n) : Nat & Nat"
  , "assert swap((0n, 0n)) == (0n, 0n) : Nat & Nat"
  , ""
  , "def main() -> Nat & Nat:"
  , "  swap((3n, 0n))"
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
