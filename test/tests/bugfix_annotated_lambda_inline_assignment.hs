{-# LANGUAGE MultilineStrings #-}

import Test

annotated_lambda_inline_assignment :: String
annotated_lambda_inline_assignment = """
-- fixed in commit 1eed35665a52f9bc793679509922e8a299a03c64
--
-- Now use annotated lambdas to help infer

def thm_fixed(A:Set) -> Σf: A->A . Σg:A->A . ∀a:A . A{g(f(a)) == a}:
  (λa:A.a,λb.b,λc.finally)

###

# can't infer type of inlined function λa.a

def thm(A:Set) -> Σf: A->A . Σg:A->A . ∀a:A . A{g(f(a)) == a}:
  (λa.a,λb.b,λc.finally)
  # (id(A),λb.b,λc.finally)

def id(B:Set, b:B) -> B:
  b

  # ✗ thm1
  # CantInfer:
  # Context:
  # - A : Set
  # - c : A
  # Location: (line 8, column 4)
  # 8 |   (λa.a,λb.b,λc.finally)
"""

main :: IO ()
main = testFileChecks annotated_lambda_inline_assignment
