{-# LANGUAGE MultilineStrings #-}

import Test

mul_succ_left_bend :: String
mul_succ_left_bend = """
def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + add(p, b)

def mul(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      0n
    case 1n + ap:
      add(b, mul(ap, b))

def mul_succ_left(a: Nat, b: Nat) -> mul(1n + a, b) == add(b, mul(a, b)) :: Nat:
  finally
"""

main :: IO ()
main = testFileChecks mul_succ_left_bend
