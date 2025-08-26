{-# LANGUAGE MultilineStrings #-}

-- fixed in: ed647c396eaa3e703c7cacbc05e0506cecdf074f
--
--  (the error was improved from CantInfer to TypeMismatch)
--  Type mismatch on a constructor pattern matching returns `CantInfer` when it should be a `Type Mismatch`.

import Test

type_error_on_ctr_mismatch :: String
type_error_on_ctr_mismatch = """
type Complex:
  case @A:
    f: (Nat -> Complex) -> Complex
  case @B:
    value: String

def String() -> Set:
  Char[]

def Check(ctx: Complex[], x: Complex) -> Complex:
  match x:
    case @A{f}:
      # Type error: should return Complex but returns a function
      λg. f(g)
    case @B{value}:
      @B{value}

def main() -> Complex:
  ctx : Complex[] = [@B{"test"}]
  x : Complex = @A{λg. g(@B{"inner"})}
  Check(ctx, x)
"""

main :: IO ()
main = testFile type_error_on_ctr_mismatch
  "Type error on constructor matching returns type mismatch, not cantInfer" $ \out err -> do
    assert (err `has` "Mismatch:")
    assert (err `has` "Goal: Complex")
    assert (err `has` "Type: Function")

