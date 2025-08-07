{-# LANGUAGE MultilineStrings #-}

-- NOT FIXED ON NEW BRANCH -> SIMILAR BUG
-- fixed in commit (BendGen-align branch) e268c925719922f390686ef0d351cd0f4245fb17

-- bug description:
-- rewrite is changing the RHS of the goal, which doesn't match the LHS of the equality term
--
-- ✓ add
-- ✗ t
-- Mismatch:
-- - 1n+add(a,1n+b)
-- - add(a,1n+b)
-- Context:
-- - a : Nat
-- - b : Nat
-- - e : Nat{add(a,1n+b)==add(a,1n+b)}
-- Location: (line 10, column 3)
-- 10 |   finally

import Test

rewrite_changes_different_term :: String
rewrite_changes_different_term = """
def add(x:Nat, y:Nat) -> Nat:
  match x:
    case 0n:
      y
    case 1n+p:
      1n+add(p,y)

def t(a:Nat, b:Nat, e: 1n+add(a,b) == add(a,1n+b) :: Nat) -> 1n+1n+add(a,b) == 1n+add(a,1n+b) :: Nat:
  rewrite e 
  finally
"""

main :: IO ()
main = testFileChecks rewrite_changes_different_term
