{-# LANGUAGE MultilineStrings #-}

import Test

vec_bend :: String
vec_bend = """
type Vec<A: Set>(N: Nat) -> Set:
  case Nil{}:
    e: N == 0n :: Nat
  case Cons{}:
    n: Nat
    h: A
    t: Vec(A,n)
    e: N == (1n+n) :: Nat

def v0 : Vec(Nat, 0n) = Nil{{==}}
def v1 : Vec(Nat, 1n) = Cons{0n, 5n, Nil{{==}}, {==}}
def v2 : Vec(Nat, 2n) = Cons{1n, 3n, Cons{0n, 7n, Nil{{==}}, {==}}, {==}}
def v3 : Vec(Bool, 3n) = Cons{2n, True, Cons{1n, False, Cons{0n, True, Nil{{==}}, {==}}, {==}}, {==}}
"""

main :: IO ()
main = testFileChecks vec_bend
