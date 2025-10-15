{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
def main : Nat =
  0n
"""

main :: IO ()
main =
  test "bend main.bend"
    [("main.bend", main_bend)]
    "running outside BendRoot must fail"
    $ \_ err -> assert (err `has` "bend must be executed from the BendRoot directory")
