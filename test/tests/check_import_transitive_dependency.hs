{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
import Tests/use_add as UseAdd

def main : Nat =
  UseAdd/use_add(5n)

assert 5n == main : Nat
"""

use_add_bend :: String
use_add_bend = """
def use_add(n: Nat) -> Nat:
  Tests/math/id(n)
"""

math_id_bend :: String
math_id_bend = """
def id(x: Nat) -> Nat:
  x
"""

main :: IO ()
main =
  test "bend main.bend"
    [ ("main.bend", main_bend)
    , ("Tests/use_add.bend", use_add_bend)
    , ("Tests/math/id.bend", math_id_bend)
    ]
    "imported module should pull transitive dependency"
    $ \_ err -> assert (err == "")
