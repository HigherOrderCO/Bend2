{-# LANGUAGE MultilineStrings #-}

import Test

check_prefixed_ctors :: String
check_prefixed_ctors = """
type A:
  case @B:
    a : Nat

type C:
  case @B:
    a : Nat
    b : Nat

def f(a : A) -> Unit:
  match a:
    case @A::B{a}: 
      ()
"""

main :: IO ()
main = testFileChecks check_prefixed_ctors
