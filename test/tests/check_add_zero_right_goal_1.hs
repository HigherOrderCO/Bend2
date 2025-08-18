{-# LANGUAGE MultilineStrings #-}

import Test

add_zero_right_goal_1_bend :: String
add_zero_right_goal_1_bend = """
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
      1n + ()
"""

main :: IO ()
main = testFileGoal add_zero_right_goal_1_bend "Nat{a$p==add(a$p,0n)}" []
