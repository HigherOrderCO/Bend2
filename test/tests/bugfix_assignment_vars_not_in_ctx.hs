{-# LANGUAGE MultilineStrings #-}

import Test

-- bug description:
-- Variables coming from let assignments not showing in the context of the error.

assignment_vars_not_in_ctx :: String
assignment_vars_not_in_ctx = """
def f() -> Unit:
  # (x,y) = (1n,2n)
  a = False
  z = 3n
  True
"""

main :: IO ()
main = testFile assignment_vars_not_in_ctx
  "Variables coming from let assignments not showing in the context" $ \out err -> do
    assert (err `has` "Mismatch:")
    assert (err `has` "Goal: Unit")
    assert (err `has` "Type: Bool")
    assert (err `has` "a : Bool")
    assert (err `has` "z : Nat")
