{-# LANGUAGE MultilineStrings #-}

import Test

-- fixed in commit: df355af377ca90afe8f2739e4f2d06b2d84992d2
--
-- Tup can't be inferred when there are dependent types.
-- Solution: Annotate the Let

annotated_lambda_help_infer :: String
annotated_lambda_help_infer = """
def thm_fixed(A:Set, B:Set) -> (∀C:Set. (A->B->C) -> C) -> Σa:A.B:
  make_pair : A -> B -> (Σa:A.B) = λa.λb.(a,b)
  λI.I(Σa:A.B, make_pair)

# can't infer when aliasing (inline use checks):

def thm(A:Set, B:Set) -> (∀C:Set. (A->B->C) -> C) -> Σa:A.B:
  make_pair = λa1.λb1.(a1,b1)
  λI.I(Σa:A.B, make_pair)

  # ✗ thm
  # CantInfer:
  # Context:
  # - A : Set
  # - B : Set
  # Location: (line 8, column 15)
  # 8 |   make_pair = λa1.λb1.(a1,b1)
"""

main :: IO ()
main = testFile annotated_lambda_help_infer
  "Annotated lambda helps type checker inference" $ \out err -> do
    assert (out `has` "✓ main::thm_fixed")
    assert (err `has` "CantInfer:")
