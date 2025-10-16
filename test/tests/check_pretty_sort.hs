{-# LANGUAGE OverloadedStrings #-}

import Test (assert, findProjectRoot, has)

import Control.Exception (finally)
import System.Directory (createDirectory, createDirectoryIfMissing, doesDirectoryExist, getEnvironment, getTemporaryDirectory, removeDirectoryRecursive)
import System.FilePath ((</>))
import System.Process (CreateProcess(..), proc, readCreateProcessWithExitCode)
import System.Exit (ExitCode(..))

main :: IO ()
main = withTempDirectory "bend-pretty-sort-test" $ \tmpDir -> do
  let bendRoot = tmpDir </> "BendRoot"
      bendFile = bendRoot </> "sort.bend"
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
                , "sort.bend"
                ]) { cwd = Just bendRoot
                    , env = Just envVars
                    }
  (exitCode, out, err) <- readCreateProcessWithExitCode cmd ""

  assert (exitCode == ExitSuccess)
  assert (null err)
  assert (out `has` "✓ sort::sort")

  final <- readFile bendFile
  assert (final == expectedOutput)

generatorSource :: String
generatorSource = unlines
  [ "def inc(n : Nat[]) -> Nat[]:"
  , "  match n:"
  , "    case []:"
  , "      return []"
  , "    case h <> t:"
  , "      return (1n + h) <> inc(t)"
  , ""
  , "gen sort(n : Nat, m : Nat[], o : Nat[]) -> Nat[] {inc}"
  , ""
  , "assert sort(4n, [2n, 1n, 3n], []) == [1n,2n,3n] : Nat[]"
  , "assert sort(5n, [4n, 3n, 1n], []) == [1n,3n,4n] : Nat[]"
  , "assert sort(5n, [3n, 4n, 2n], []) == [2n,3n,4n] : Nat[]"
  , ""
  , "def main() -> Nat[]:"
  , "  sort(5n, [4n, 3n, 2n, 1n], [])"
  ]

expectedOutput :: String
expectedOutput = unlines
  [ ""
  , "def inc(n : Nat[]) -> Nat[]:"
  , "  match n:"
  , "    case []:"
  , "      return []"
  , "    case h <> t:"
  , "      return (1n + h) <> inc(t)"
  , ""
  , "def sort(n: Nat, m: Nat[], o: Nat[]) -> Nat[]:"
  , "  match n:"
  , "    case 0n:"
  , "      return []"
  , "    case 1n+p:"
  , "      match m:"
  , "        case []:"
  , "          return inc(sort(p, o, []))"
  , "        case h <> t:"
  , "          match h:"
  , "            case 0n:"
  , "              return 0n <> sort(1n+p, t, o)"
  , "            case 1n+p1:"
  , "              return sort(1n+p, t, p1 <> o)"
  , ""
  , ""
  , ""
  , "assert sort(4n, [2n, 1n, 3n], []) == [1n,2n,3n] : Nat[]"
  , "assert sort(5n, [4n, 3n, 1n], []) == [1n,3n,4n] : Nat[]"
  , "assert sort(5n, [3n, 4n, 2n], []) == [2n,3n,4n] : Nat[]"
  , ""
  , "def main() -> Nat[]:"
  , "  sort(5n, [4n, 3n, 2n, 1n], [])"
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
