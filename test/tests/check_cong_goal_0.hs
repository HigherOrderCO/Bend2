{-# LANGUAGE MultilineStrings #-}

import Test

cong_goal_0_bend :: String
cong_goal_0_bend = """
def cong
  ( A: Set
  , B: Set
  , a: A
  , b: A
  , f: A -> B
  , e: a == b :: A
  ) -> f(a) == f(b) :: B:
  ()
"""

main :: IO ()
main = testFileGoal cong_goal_0_bend "f(a)==f(b) : B" []
