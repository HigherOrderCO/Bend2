{-# LANGUAGE MultilineStrings #-}

import Test

-- Test: Auto-import when function name matches file name
-- Verifies that auto-import works when the function name exactly matches the module name

c_bend :: String
c_bend = """
type C:
  case @X:
  case @Y:

def x() -> C:
  @X

def y() -> C:
  @Y
"""

main_bend :: String
main_bend = """
def main() -> C:
  @X 
"""

main :: IO ()
main = test "bend main.bend" 
  [("main.bend", main_bend), ("C.bend", c_bend)]
  "auto-import should work when function name matches file name"
  $ \out err -> do
    assert (err == "")
