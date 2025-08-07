{-# LANGUAGE MultilineStrings #-}

import Test

add_zero_right_goal_0_bend :: String
add_zero_right_goal_0_bend = """
def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + add(p, b)

def add_zero_right(a: Nat) -> a == add(a,0n) :: Nat:
  match a:
    case 0n:
      ()
    case 1n + ap:
      1n + add_zero_right(ap)
"""

main :: IO ()
main = testFileGoal add_zero_right_goal_0_bend "0n==0n "Nat" []
