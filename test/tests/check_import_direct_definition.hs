{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
import Tests/math::answer as ans

def main : Nat =
  ans

assert 42n == ans : Nat
assert 42n == main : Nat
"""

math_bend :: String
math_bend = """
def answer : Nat =
  42n
"""

main :: IO ()
main = do
  projectDir <- findProjectRoot
  let cmd = "(cd BendRoot && cabal run -v0 bend --project-dir=" ++ show projectDir ++ " -- main.bend)"
  test cmd
    [ ("BendRoot/main.bend", main_bend)
    , ("BendRoot/Tests/math.bend", math_bend)
    ]
    "importing a direct definition via FQN succeeds"
    $ \_ err -> assert (err == "")
