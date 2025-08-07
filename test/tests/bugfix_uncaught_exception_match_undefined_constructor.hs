{-# LANGUAGE MultilineStrings #-}

-- bug description:
-- see https://github.com/HigherOrderCO/Bend2/issues/22

import Test

prove_false :: String
prove_false = """
def t(a:Nat) -> Unit:
  match a:
    case 0n:
      ()
    case Undefined{x}:
      ()
"""

main :: IO ()
main = testFileWithTimeout prove_false
  "Proving False should not be allowed" (\out err -> do
    assert (not (err `has` "Uncaught exception"))
    assert (err `has` "Location:")
    assert (not (err == ""))) 3

