{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
import Tests/missing::ghost as ghost

def main : Nat =
  ghost()
"""

main :: IO ()
main = do
  projectDir <- findProjectRoot
  let cmd = "(cd BendRoot && cabal run -v0 bend --project-dir=" ++ show projectDir ++ " -- main.bend)"
  test cmd
    [("BendRoot/main.bend", main_bend)]
    "missing imports should raise an error"
    $ \_ err -> do
      assert (err `has` "unable to locate module 'Tests/missing'")
