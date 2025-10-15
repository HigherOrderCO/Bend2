{-# LANGUAGE MultilineStrings #-}

import Test

-- Bug description:
--
-- aliasing logic was not removing the '/' suffix, which caused refs to be unavailable
-- errors were not being handled very good.
--   1. Parses the import and stores "add/" => "fixme/add_for_import/"
--   2. When parsing add, checks for exact match: M.lookup "add/" finds "fixme/add_for_import/"
--   3. Strips the trailing "/" to get "fixme/add_for_import"
--   4. Auto-import system loads the definition from fixme/add_for_import.bend


main_bend :: String
main_bend = """
import fixme/add_for_import as add

def f() -> Nat -> Nat -> Nat:
  add
"""

add_for_import_bend :: String
add_for_import_bend = """
def add_for_import(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n+p:
      add_for_import(p,b)
"""

main :: IO ()
main = test "bend main.bend" 
  [("main.bend", main_bend), ("fixme/add_for_import.bend", add_for_import_bend)]
  "import with alias should work"
  $ \out err -> do
    assert (err == "")
