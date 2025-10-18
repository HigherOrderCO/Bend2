module Main where

import System.Environment (getArgs)
import Core.CLI (processFile, processFileToJS, processFileToHVM, listDependencies, getGenDeps, processFileToCore, processFileToHS)
import Core.Adjust.ReduceEtas
import Package.Publish (runPublishCommand, runBumpCommand, AuthMode(..))

-- | Show usage information
showUsage :: IO ()
showUsage = do
  putStrLn "Usage:"
  putStrLn "  bend publish [--manual-cookie] [module]"
  putStrLn "  bend bump [--manual-cookie] module"
  putStrLn "  bend <file.bend> [options]"
  putStrLn ""
  putStrLn "Options:"
  putStrLn "  --to-javascript    Compile to JavaScript"
  putStrLn "  --to-hvm           Compile to HVM"
  putStrLn "  --to-haskell       Compile to Haskell"
  putStrLn "  --list-dependencies List all dependencies (recursive)"
  putStrLn "  --get-gen-deps      Get dependencies for code generation"
  putStrLn "  --show-core        Returns the book of Core terms"

-- | Main entry point
main :: IO ()
main = do
  args <- getArgs
  case args of
    ("publish":rest)                     -> runPublish rest
    ("bump":rest)                        -> runBump rest
    [file, "--to-javascript"] | ".bend"    `isSuffixOf` file -> processFileToJS file
    [file, "--to-javascript"] | ".bend.py" `isSuffixOf` file -> processFileToJS file
    [file, "--to-hvm"] | ".bend"    `isSuffixOf` file -> processFileToHVM file
    [file, "--to-hvm"] | ".bend.py" `isSuffixOf` file -> processFileToHVM file
    [file, "--to-haskell"] | ".bend"    `isSuffixOf` file -> processFileToHS file
    [file, "--to-haskell"] | ".bend.py" `isSuffixOf` file -> processFileToHS file
    [file, "--list-dependencies"] | ".bend"    `isSuffixOf` file -> listDependencies file
    [file, "--list-dependencies"] | ".bend.py" `isSuffixOf` file -> listDependencies file
    [file, "--get-gen-deps"] | ".bend"    `isSuffixOf` file -> getGenDeps file
    [file, "--get-gen-deps"] | ".bend.py" `isSuffixOf` file -> getGenDeps file
    [file, "--show-core"] | ".bend"    `isSuffixOf` file -> processFileToCore file
    [file, "--show-core"] | ".bend.py" `isSuffixOf` file -> processFileToCore file
    [file] | ".bend"    `isSuffixOf` file -> processFile file
    [file] | ".bend.py" `isSuffixOf` file -> processFile file
    otherwise                             -> showUsage
  where isSuffixOf suffix str = reverse suffix == take (length suffix) (reverse str)

        runPublish xs =
          let (mode, rest) = withAuthFlag xs
          in case rest of
               []           -> runPublishCommand mode Nothing
               [moduleName] -> runPublishCommand mode (Just moduleName)
               _            -> showUsage

        runBump xs =
          let (mode, rest) = withAuthFlag xs
          in case rest of
               [moduleName] -> runBumpCommand mode moduleName
               _            -> showUsage

        withAuthFlag :: [String] -> (AuthMode, [String])
        withAuthFlag xs =
          case break (== "--manual-cookie") xs of
            (before, _:after) -> (AuthManual, before ++ after)
            (before, [])      -> (AuthAuto, before)

-- main :: IO ()
-- main = testEtaForm
