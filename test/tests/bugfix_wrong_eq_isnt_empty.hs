{-# LANGUAGE MultilineStrings #-}

-- fixed in commit (BenGen-align branch) 6fc55e28e93f25f6f3f2926728908be1e6bb3ba2

-- bug description:
-- 0 == 1 is not behaving like a proof of Empty
--
-- ✗ t
-- Mismatch:
-- - Goal: ∀e:Nat{0n==1n+0n}. A
-- - Type: Empty -> Set
-- Context:
-- - A : Set
-- Location: (line 0, column 0)-

import Test

wrong_eq_isnt_empty :: String
wrong_eq_isnt_empty = """
def t(A:Set, e: 0n==1n :: Nat) -> A:
  λ{}(e)
"""

main :: IO ()
main = testFileChecks wrong_eq_isnt_empty
