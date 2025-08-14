{-# LANGUAGE MultilineStrings #-}

import Test

-- The following code gives a can't infer, when it should instead trivially check,
-- since emp appears in the context with type Empty.

cant_infer_indirectly_derived_empty :: String
cant_infer_indirectly_derived_empty = """
def t_(A: Set, e: Empty) -> A:
  absurd e

def t(A: Set, e: Nat{0n == 0n} -> Empty) -> A:
  t_(A, e(finally))
"""

-- gives:
-- CantInfer:
-- Context:
-- - A : Set
-- - e : Nat{0n==0n} -> Empty
-- - emp : Empty
-- Location: (line 3, column 3)
-- 3 |   ~emp{}

-- The same issue doesn't happen if we match on an Empty value directly as an argument, as in
-- def u(A: Set, emp: Empty) -> A:
  -- ~emp{}

main :: IO ()
main = testFileChecks cant_infer_indirectly_derived_empty

