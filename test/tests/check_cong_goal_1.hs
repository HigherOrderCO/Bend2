{-# LANGUAGE MultilineStrings #-}

import Test

cong_goal_1_bend :: String
cong_goal_1_bend = """
def cong
  ( A: Set
  , B: Set
  , a: A
  , b: A
  , f: A -> B
  , e: a == b :: A
  ) -> f(a) == f(b) :: B:
  rewrite e
  ()
"""

main :: IO ()
main = testFileGoal cong_goal_1_bend "f(b)==f(b) : B" []
