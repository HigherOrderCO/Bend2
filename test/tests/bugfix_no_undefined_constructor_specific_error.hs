{-# LANGUAGE MultilineStrings #-}

import Test

-- bug description:
-- see https://github.com/HigherOrderCO/Bend2/issues/23
--

no_undefined_constructor_error :: String
no_undefined_constructor_error = """
def main() -> Unit:
  Undefined{}
"""

main :: IO ()
main = testFile no_undefined_constructor_error
  "" $ \out err -> do
    assert (err `has` "Undefined")
    assert (err `has` "Undefined{}")
    assert (err `has` "Location: ")
