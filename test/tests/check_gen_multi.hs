{-# LANGUAGE MultilineStrings #-}

import Test

gen_multi :: String
gen_multi = """
gen mul2(n: Nat) -> Nat

assert mul2(2n) == 4n : Nat
assert mul2(3n) == 6n : Nat

gen add1(n: Nat) -> Nat

assert add1(0n) == 1n : Nat
assert add1(2n) == 3n : Nat

def main() -> Nat:
  mul2(add1(2n))
"""

main :: IO ()
main = testFile gen_multi "multi gen synthesizes both definitions" $ \out err -> do
  assert (err == "")
  assert (out `has` "6n")
