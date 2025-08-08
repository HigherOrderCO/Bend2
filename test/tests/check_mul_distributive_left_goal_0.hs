{-# LANGUAGE MultilineStrings #-}

import Test

mul_distributive_left_goal_0_bend :: String
mul_distributive_left_goal_0_bend = """
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

def mul_distributive_left(n: Nat, m: Nat, k: Nat) -> mul(n, add(m,k)) == add(mul(n,m), mul(n,k)) :: Nat:
  match n:
    case 0n:
      ()
    case 1n + p:
      finally
"""

main :: IO ()
main = testFileGoal mul_distributive_left_goal_0_bend "0n==0n : Nat" []
