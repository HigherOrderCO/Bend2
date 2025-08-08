{-# LANGUAGE MultilineStrings #-}

import Test

mul_distributive_left_goal_7_bend :: String
mul_distributive_left_goal_7_bend = """
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

def add_associative(a: Nat, b: Nat, c: Nat) -> add(add(a,b), c) == add(a, add(b,c)) :: Nat:
  match a:
    case 0n:
      {==}
    case 1n + ap:
      1n + add_associative(ap, b, c)

def add_zero_right(a: Nat) -> a == add(a,0n) :: Nat:
  match a:
    case 0n:
      {==}
    case 1n + ap:
      1n + add_zero_right(ap)

def add_succ_right(a: Nat, b: Nat) -> add(a,1n+b) == (1n+add(a,b)) :: Nat:
  match a:
    case 0n:
      1n + {==}
    case 1n + ap:
      1n + add_succ_right(ap,b)

def add_commutative(a: Nat, b: Nat) -> add(a,b) == add(b,a) :: Nat:
  match a:
    case 0n:
      add_zero_right(b)
    case 1n+ap:
      e0 = add_commutative(ap, b)
      e1 = add_succ_right(b, ap)
      rewrite e0
      rewrite e1
      1n + {==}

def mul_distributive_left(n: Nat, m: Nat, k: Nat) -> mul(n, add(m,k)) == add(mul(n,m), mul(n,k)) :: Nat:
  match n:
    case 0n:
      {==}
    case 1n + p:
      rewrite mul_distributive_left(p, m, k)
      rewrite add_associative(m, k, add(mul(p,m),mul(p,k)))
      rewrite add_commutative(k, add(mul(p,m),mul(p,k)))
      rewrite add_associative(mul(p,m), mul(p,k), k)
      rewrite add_commutative(mul(p,k), k)
      rewrite add_associative(m, mul(p,m), add(k,mul(p,k)))
      ()
"""

main :: IO ()
main = testFileGoal mul_distributive_left_goal_7_bend "add(m,add(mul(p,m),add(k,mul(p,k))))==add(m,add(mul(p,m),add(k,mul(p,k)))) : Nat" []
