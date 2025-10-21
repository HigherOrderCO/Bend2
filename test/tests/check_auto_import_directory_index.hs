{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
def main : Nat =
  Lib/Numbers

assert 123n == Lib/Numbers : Nat
assert 123n == main : Nat
"""

numbers_bend :: String
numbers_bend = """
def Numbers : Nat =
  123n
"""

main :: IO ()
main =
  test "bend main.bend"
    [ ("main.bend", main_bend)
    , ("Lib/Numbers/_.bend", numbers_bend)
    ]
    "auto-import resolves directory index module"
    $ \_ err -> assert (err == "")
