{-# LANGUAGE MultilineStrings #-}

import Test

add_commutative_goal_4_bend :: String
add_commutative_goal_4_bend = """
def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + add(p, b)

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
      1n + ()
"""

main :: IO ()
main = testFileGoal add_commutative_goal_4_bend "add(b,ap)==add(b,ap) : Nat" []
