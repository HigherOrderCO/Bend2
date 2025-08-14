{-# LANGUAGE MultilineStrings #-}

import Test

mismatch_default_case :: String
mismatch_default_case = """
type Type:
  case @A:
  case @B:

def f(t : Type) -> Type:
  match t:
    case @A{}:
      @B{}
    case x:
      x
"""

main :: IO ()
main = testFileChecks mismatch_default_case
