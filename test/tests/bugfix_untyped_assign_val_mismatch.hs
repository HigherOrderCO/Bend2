{-# LANGUAGE MultilineStrings #-}

import Test

-- bug description:
-- see https://github.com/HigherOrderCO/Bend2/issues/19
--
-- The following code gives a mismatch type error in the value
-- of the variable ind at assignment, when no annotation means that
-- this variable has no type that must be satisfied

untyped_assign_val_mismatch :: String
untyped_assign_val_mismatch = """
type ListNat:
  case Nil{}:
  case Cons{}: h: Nat
              t: ListNat
def t(a:Nat, l:ListNat) -> Bool:
  match l:
    case Nil{}: True
    case Cons{h,t}:
      ind = t(h,t)
      True
"""

-- ✓ ListNat
-- ✗ t
-- Mismatch:
-- - Goal: _ -> _
-- - Type: ListNat
-- Context:
-- - a : Nat
-- - h : Nat
-- - t : ListNat
-- Location: (line 9, column 13)
-- 9 |       ind = t(h,t)

main :: IO ()
main = testFileChecks untyped_assign_val_mismatch
