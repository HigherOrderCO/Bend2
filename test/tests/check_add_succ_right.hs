{-# LANGUAGE MultilineStrings #-}

import Test

add_succ_right_bend :: String
add_succ_right_bend = """
def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + add(p, b)

def add_succ_right(a: Nat, b: Nat) -> add(a,1n+b) == (1n+add(a,b)) :: Nat:
  match a:
    case 0n:
      1n + {==}
    case 1n + ap:
      1n + add_succ_right(ap,b)
"""

main :: IO ()
main = testFileChecks add_succ_right_bend
