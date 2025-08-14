{-# LANGUAGE MultilineStrings #-}

import Test

-- NOT FIXED
--
-- bug description:

-- OLD SOLUTION:
-- The issue was that, once you create an an alias, like `Y = A`, Bend replaces
-- all occurrences of `A` by `Y`, in the *goal* and *context*. but if you then
-- explicitly write `A` (again) in the term itself, it won't be replaced, and you
-- get that error. Fixing this "error" require doing `rewrite` in the term too,
-- but that's complicated, because rewrites uses 'whnf', which can lose info
-- (like Anns and Locs) and also cause infinite loops. I've solved this by doing
-- a rewrite with lv=0 on the term, but this sounds risky.


alias_redeclaration_discrepancy :: String
alias_redeclaration_discrepancy = """
def exists(A : Set, P: A -> Set) -> Set:
  ∀C:Set . ((∀a:A . (P(a) -> C)) -> C)

def exists_intro : ∀A: Set . (∀P: A -> Set . (∀a:A . (∀pa:P(a) . (exists(A,P))))) =
  λA.λP.λa.λpa.λC.λI.I(a)(pa)

def is_left_inverse<A,B>(g: B->A, f:A->B) -> Set:
  ∀a:A . A{g(f(a)) == a}

def has_left_inverse<A,B>(f: A->B) -> Set:
  exists(B->A, λg . is_left_inverse<A,B>(g,f)) 

def dettach<A>(t:Σa:A.Unit) -> A:
  match t:
    case (a,b): a

def attach<A>(a:A) -> Σa:A.Unit:
  (a,())

def dettach_left_inv_attach<A>() -> is_left_inverse<A,Σa:A.Unit>(dettach<A>,attach<A>):
  λa.finally

# THIS DOESNT WORK:

def attach_has_left_inv<A>() -> has_left_inverse<A,Σa:A.Unit>(attach<A>):
  Y = A
  exists_intro((Σa:A.Unit) -> Y, λh.is_left_inverse<Y,(Σa:Y.Unit)>(h,attach<Y>), dettach<Y>, dettach_left_inv_attach<Y>())
"""

main :: IO ()
main = testFileChecks alias_redeclaration_discrepancy
