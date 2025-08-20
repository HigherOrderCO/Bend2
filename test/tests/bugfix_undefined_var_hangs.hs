{-# LANGUAGE MultilineStrings #-}

-- This program with an undefined variable hangs.

import Test

undefined_var_hangs :: String
undefined_var_hangs = """
def main() -> Nat:
  return a
"""

main :: IO ()
main = testFileWithTimeout undefined_var_hangs
  "Undefined variable on main hangs" (\out err -> do
    assert (err `has` "Unbound")
    assert (err `has` "a")
    assert (not (err == ""))) 1


