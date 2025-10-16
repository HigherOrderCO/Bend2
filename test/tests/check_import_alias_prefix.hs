{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
import Tests/math/id as Math

def twice(n: Nat) -> Nat:
  Math/id(Math/id(n))

def main : Nat =
  twice(7n)

assert 7n == Math/id(7n) : Nat
assert 7n == twice(7n) : Nat
assert 7n == main : Nat
"""

math_id_bend :: String
math_id_bend = """
def id(x: Nat) -> Nat:
  x
"""

main :: IO ()
main =
  test "bend main.bend"
    [ ("main.bend", main_bend)
    , ("Tests/math/id.bend", math_id_bend)
    ]
    "prefix alias rewrites references correctly"
    $ \_ err -> assert (err == "")
