{-# LANGUAGE MultilineStrings #-}

import Test

add_associative_goal_2_bend :: String
add_associative_goal_2_bend = """
def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + add(p, b)

def add_associative(a: Nat, b: Nat, c: Nat) -> Nat{add(add(a,b), c) == add(a, add(b,c))}:
  match a:
    case 0n:
      {==}
    case 1n + ap:
      1n + ()
"""

main :: IO ()
main = testFileGoal add_associative_goal_2_bend "Nat{add(add(a$p,b),c)==add(a$p,add(b,c))}" []
