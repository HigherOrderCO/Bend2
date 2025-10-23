{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
alias Tests/math as Math
import Math/id as Id
import Math/zero as Zero

def main : Nat =
  Id(Zero)

assert 0n == Zero : Nat
assert 0n == main : Nat
"""

math_id_bend :: String
math_id_bend = """
def id(x: Nat) -> Nat:
  x
"""

math_zero_bend :: String
math_zero_bend = """
def zero : Nat =
  0n
"""

main :: IO ()
main =
  test "bend main.bend"
    [ ("main.bend", main_bend)
    , ("Tests/math/id.bend", math_id_bend)
    , ("Tests/math/zero.bend", math_zero_bend)
    ]
    "alias prefixes expand for subsequent imports"
    $ \_ err -> assert (err == "")
