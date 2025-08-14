{-# LANGUAGE MultilineStrings #-}

import Test

-- bug description:
-- see https://github.com/HigherOrderCO/Bend2/issues/13
--
-- scoping of variables when printing a context isn't respected.
-- notice in the error that in A{(a)((a,()))==a}
-- the first `a` should be (Σa:A. Unit) -> A, and the second, A.
-- both `a` there are actually the same variable
-- Suggestion: add depth: 
--  - Goal: Σa:((Σa:A^0. Unit) -> A^0). ∀a:A^0. A^0{(a^0)((a^0,()))==a^0}

scoping_not_respected_on_ctx :: String
scoping_not_respected_on_ctx = """
def exists(A: Set, P:A->Set) -> Set:
  Σa:A.P(a)

def thm(A:Set) -> exists((Σa:A.Unit)->A, λf.(∀a:A. A{f((a,())) == a})):
  ()

  # ✗ thm
  # Mismatch:
  # - Goal: Σa:((Σa:A. Unit) -> A). ∀a:A. A{(a)((a,()))==a}
  # - Type: Unit
  # Context:
  # - A : Set
  # Location: (line 16, column 3)
  # 16 |   ()
"""

main :: IO ()
main = testFile scoping_not_respected_on_ctx
  "Scoping not respected when printing context" $ \out err -> do
    assert (err `has` "Σa^0:((Σa^0:A. Unit) -> A). ∀a^1:A. A{(a^0)((a^1,()))==a^1}")
