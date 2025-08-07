{-# LANGUAGE MultilineStrings #-}

import Test

-- fixed in commit 1d6d800fc0ed1873fc91b84111ab1a41d2e2ba90
--
-- note: (a+b) for Nats requires Nat/add in context
--
-- bug description:
-- (a+b) == add(a,b) can't be proven because (a+b) parses as (Op2 ADD)
--
--   ✗ f
--   Mismatch:
--   - Goal: Num
--   - Type: Nat
--   Context:
--   - a : Nat
--   - b : Nat
--   Location: (line 17, column 3)
--   17 |   a+b

infix_nat_add_isnt_op2 :: String
infix_nat_add_isnt_op2 = """
def Nat/add(a:Nat, b:Nat) -> Nat:
  match a:
    case 0n: b
    case 1n+p: 1n+Nat/add(p,b)

def add_x_y (a:Nat, b:Nat) -> (a+b) == Nat/add(a,b) :: Nat:
  match a:
    case 0n:
      finally
    case 1n + p:
      finally
"""

main :: IO ()
main = testFileChecks infix_nat_add_isnt_op2
