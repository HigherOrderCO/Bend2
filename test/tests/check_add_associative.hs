{-# LANGUAGE MultilineStrings #-}

import Test

add_associative_bend :: String
add_associative_bend = """
def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + add(p, b)

def add_associative(a: Nat, b: Nat, c: Nat) -> add(add(a,b), c) == add(a, add(b,c)) :: Nat:
  match a:
    case 0n:
      {==}
    case 1n + ap:
      1n + add_associative(ap, b, c)
"""

main :: IO ()
main = testFileChecks add_associative_bend
