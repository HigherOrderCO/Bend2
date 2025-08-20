{-# LANGUAGE MultilineStrings #-}

import Test

-- bug description:
-- see https://github.com/HigherOrderCO/Bend2/issues/21
--
-- The following code results in a type mismatch error which is lacking a location,
-- but the actual mistake is a missing argument to the @Wrap constructor in the case clause

missing_constructor_bad_error :: String
missing_constructor_bad_error = """
type Wrapper:
  case @Wrap: a :Nat

def t(a:Wrapper) -> Nat:
  match a:
    case @Wrap: 0n
"""

-- ✓ Wrapper
-- ✗ t
-- Mismatch:
-- - Goal: ∀y:(Σa:Nat. Unit). Nat
-- - Type: Unit -> Set
-- Context:
-- Location: (line 0, column 0)

main :: IO ()
main = testFile missing_constructor_bad_error
  "Missing constructor gives a mismatch, bad erroring." $ \out err -> do
    assert (err `has` "missing constructor")
    assert (not (err `has` "Mismatch"))

