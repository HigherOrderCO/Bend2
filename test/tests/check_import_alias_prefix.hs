{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
import Tests/math as Math

def twice(n: Nat) -> Nat:
  Math::id(Math::id(n))

def main : Nat =
  twice(7n)

assert 7n == Math::id(7n) : Nat
assert 7n == twice(7n) : Nat
assert 7n == main : Nat
"""

math_bend :: String
math_bend = """
def id(x: Nat) -> Nat:
  x
"""

main :: IO ()
main = do
  projectDir <- findProjectRoot
  let cmd = "(cd BendRoot && cabal run -v0 bend --project-dir=" ++ show projectDir ++ " -- main.bend)"
  test cmd
    [ ("BendRoot/main.bend", main_bend)
    , ("BendRoot/Tests/math.bend", math_bend)
    ]
    "prefix alias rewrites references correctly"
    $ \_ err -> assert (err == "")
