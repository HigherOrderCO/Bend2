{-# LANGUAGE MultilineStrings #-}

import Test

div2_mul2_inverse_bend :: String
div2_mul2_inverse_bend = """
def mul2(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n + p:
      2n + mul2(p)

def div2(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n:
      0n
    case 2n + p:
      1n + div2(p)

def div2_mul2_inverse(n: Nat) -> Nat{div2(mul2(n)) == n}:
  match n:
    case 0n:
      {==}
    case 1n + p:
      1n + div2_mul2_inverse(p)
"""

main :: IO ()
main = testFileChecks div2_mul2_inverse_bend
