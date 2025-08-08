{-# LANGUAGE MultilineStrings #-}

import Test

succ_not_zero_bend :: String
succ_not_zero_bend = """
def Not(A: Set) -> Set:
  A -> Empty

def succ_not_zero(n: Nat) -> Not(0n == (1n+n) :: Nat):
  λe. absurd e
"""

main :: IO ()
main = testFileChecks succ_not_zero_bend
