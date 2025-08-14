{-# LANGUAGE MultilineStrings #-}

import Test

-- bug description:
-- Fixed on pr: https://github.com/HigherOrderCO/Bend2/pull/28

missing_constructor_bad_error :: String
missing_constructor_bad_error = """
type A:
  case @B:
    a : Nat

type C:
  case @B:
    a : Nat
    b : Nat

def f(a : A) -> Unit:
  match a:
    case @B{a, b}: 
      ()
"""

main :: IO ()
main = testFile missing_constructor_bad_error
  "Missing constructor gives a mismatch, bad erroring." $ \out err -> do
    assert (err `has` "Ambiguous constructor name: `B{..}`. Please prefix it with its type name.")
    assert (not (err `has` "Mismatch"))

