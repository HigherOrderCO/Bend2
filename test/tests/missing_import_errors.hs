{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
import Tests/missing/ghost as ghost

def main : Nat =
  ghost()
"""

main :: IO ()
main =
  test "bend main.bend"
    [("main.bend", main_bend)]
    "missing imports should raise an error"
    $ \_ err -> do
      assert (err `has` "unable to locate module 'Tests/missing/ghost'")
