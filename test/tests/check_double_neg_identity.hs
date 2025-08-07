{-# LANGUAGE MultilineStrings #-}

import Test

double_neg_identity_bend :: String
double_neg_identity_bend = """
def neg(x: Bool) -> Bool:
  if x:
    False
  else:
    True

def double_neg_identity(x: Bool) -> neg(neg(x)) == x :: Bool:
  if x:
    {==}
  else:
    {==}
"""

main :: IO ()
main = testFileChecks double_neg_identity_bend
