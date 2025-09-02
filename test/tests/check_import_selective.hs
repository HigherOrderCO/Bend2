{-# LANGUAGE MultilineStrings #-}

import Test

-- Test: Selective imports (from Module import name)
-- Verifies that selective imports work correctly and that
-- non-imported functions from the same module are not accessible

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
  b
"""

main :: IO ()
main = test "bend b.bend" 
  [("b.bend", b_bend), ("C.bend", c_bend), ("D.bend", d_bend)]
  "selective import should work, y() accessible but x() not"
  $ \out err -> do
    assert (err == "")