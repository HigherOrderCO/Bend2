{-# LANGUAGE MultilineStrings #-}

import Test

mul_zero_right_goal_2_bend :: String
mul_zero_right_goal_2_bend = """
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

def mul_zero_right(n: Nat) -> mul(n, 0n) == 0n :: Nat:
  match n:
    case 0n:
      finally
    case 1n + p:
      rewrite mul_zero_right(p)
      ()
"""

main :: IO ()
main = testFileGoal mul_zero_right_goal_2_bend "0n==0n : Nat" []
