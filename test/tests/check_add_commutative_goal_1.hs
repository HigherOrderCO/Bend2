{-# LANGUAGE MultilineStrings #-}

import Test

add_commutative_goal_1_bend :: String
add_commutative_goal_1_bend = """
def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + add(p, b)

def add_zero_right(a: Nat) -> Nat{a == add(a,0n)}:
  match a:
    case 0n:
      {==}
    case 1n + ap:
      1n + add_zero_right(ap)

def add_succ_right(a: Nat, b: Nat) -> Nat{add(a,1n+b) == (1n+add(a,b))}:
  match a:
    case 0n:
      1n + {==}
    case 1n + ap:
      1n + add_succ_right(ap,b)

def add_commutative(a: Nat, b: Nat) -> Nat{add(a,b) == add(b,a)}:
  match a:
    case 0n:
      add_zero_right(b)
    case 1n+ap:
      ()
"""

main :: IO ()
main = testFileGoal add_commutative_goal_1_bend "Nat{1n+add(a$p,b)==add(b,1n+a$p)}" []
