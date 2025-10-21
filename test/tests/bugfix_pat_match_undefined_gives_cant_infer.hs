{-# LANGUAGE MultilineStrings #-}

import Test

-- bug description:
-- see https://github.com/HigherOrderCO/Bend2/issues/15
--

pat_match_undefined_gives_cant_infer :: String
pat_match_undefined_gives_cant_infer = """
def t(n:Nat) -> Nat:
  match undefined:
    case 0n: ()
    case 1n+p: ()
"""

-- ✗ t
-- CantInfer:
-- Context:
-- - n : Nat
-- Location: (line 2, column 3)
-- 2 |   match undefined:
-- 3 |     case 0n: ()
-- 4 |     case 1n+p: ()

main :: IO ()
main = testFile pat_match_undefined_gives_cant_infer
  "Pattern matchin on undefined gives cant infer instead of undefined val." $ \out err -> do
    assert (err `has` "Undefined")
    assert (not (err `has` "Mismatch"))
    assert (not (err `has` "CantInfer"))


