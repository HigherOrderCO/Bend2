{-# LANGUAGE MultilineStrings #-}

import Test

mul_distributive_left_goal_1_bend :: String
mul_distributive_left_goal_1_bend = """
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

def mul_distributive_left(n: Nat, m: Nat, k: Nat) -> Nat{mul(n, add(m,k)) == add(mul(n,m), mul(n,k))}:
  match n:
    case 0n:
      {==}
    case 1n + p:
      ()
"""

main :: IO ()
main = testFileGoal mul_distributive_left_goal_1_bend "Nat{add(add(m,k),mul(n$p,add(m,k)))==add(add(m,mul(n$p,m)),add(k,mul(n$p,k)))}" []
