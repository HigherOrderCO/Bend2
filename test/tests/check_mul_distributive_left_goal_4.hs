{-# LANGUAGE MultilineStrings #-}

import Test

mul_distributive_left_goal_4_bend :: String
mul_distributive_left_goal_4_bend = """
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

def add_associative(a: Nat, b: Nat, c: Nat) -> Nat{add(add(a,b), c) == add(a, add(b,c))}:
  match a:
    case 0n:
      {==}
    case 1n + ap:
      1n + add_associative(ap, b, c)

def add_commutative(a: Nat, b: Nat) -> Nat{add(a,b) == add(b,a)}:
  match a:
    case 0n:
      ()
    case 1n+ap:
      ()

def mul_distributive_left(n: Nat, m: Nat, k: Nat) -> Nat{mul(n, add(m,k)) == add(mul(n,m), mul(n,k))}:
  match n:
    case 0n:
      {==}
    case 1n + p:
      rewrite mul_distributive_left(p, m, k)
      rewrite add_associative(m, k, add(mul(p,m),mul(p,k)))
      rewrite add_commutative(k, add(mul(p,m),mul(p,k)))
      ()
"""

main :: IO ()
main = testFileGoal mul_distributive_left_goal_4_bend "Nat{add(m,add(add(mul(n$p,m),mul(n$p,k)),k))==add(add(m,mul(n$p,m)),add(k,mul(n$p,k)))}" []
