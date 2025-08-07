{-# LANGUAGE MultilineStrings #-}

import Test

add_zero_left_bend :: String
add_zero_left_bend = """
def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + add(p, b)

def add_zero_left(b: Nat) -> add(0n, b) == b :: Nat:
  {==}
"""

main :: IO ()
main = testFileChecks add_zero_left_bend
