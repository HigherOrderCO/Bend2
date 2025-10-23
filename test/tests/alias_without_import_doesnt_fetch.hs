{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
alias Missing/module as M

def main : Nat =
  0n

assert 0n == main : Nat
"""

main :: IO ()
main =
  test "bend main.bend"
    [ ("main.bend", main_bend)
    ]
    "alias directives do not trigger module loading"
    $ \_ err -> assert (err == "")
