{-# LANGUAGE MultilineStrings #-}

import Test

-- Test: Blocking non-matching auto-imports
-- Verifies that functions that don't match the module name cannot be auto-imported
-- In this case, x() from C.bend should NOT be auto-importable

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

d_bend :: String
d_bend = """
def test() -> Nat:
  0n
"""

b_bend :: String
b_bend = """
import D
from C import y

def main() -> C:
  a = D::test()
  b = y()
  c = x()
  c
"""

main :: IO ()
main = test "bend b.bend" 
  [("b.bend", b_bend), ("C.bend", c_bend), ("D.bend", d_bend)]
  "x() should not be accessible (not imported, can't auto-import)"
  $ \out err -> do
    assert (err /= "")  -- There should be an error
    assert (err `has` "Undefined")  -- Check for the undefined error
    assert (err `has` "x")
