{-# LANGUAGE MultilineStrings #-}

import Test

cong_bend :: String
cong_bend = """
def cong
  ( A: Set
  , B: Set
  , a: A
  , b: A
  , f: A -> B
  , e: a == b :: A
  ) -> f(a) == f(b) :: B:
  rewrite e
  {==}
"""

main :: IO ()
main = testFileChecks cong_bend
