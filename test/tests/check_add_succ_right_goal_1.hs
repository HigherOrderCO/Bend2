{-# LANGUAGE MultilineStrings #-}

import Test

add_succ_right_goal_1_bend :: String
add_succ_right_goal_1_bend = """
def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + add(p, b)

def add_succ_right(a: Nat, b: Nat) -> Nat{add(a,1n+b) == (1n+add(a,b))}:
  match a:
    case 0n:
      1n + {==}
    case 1n + ap:
      1n + ()
"""

main :: IO ()
main = testFileGoal add_succ_right_goal_1_bend "Nat{add(a$p,1n+b)==1n+add(a$p,b)}" []
