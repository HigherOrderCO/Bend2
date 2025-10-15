{-# LANGUAGE MultilineStrings #-}

import Test

slash_definition_bend :: String
slash_definition_bend = """
def Nat/add() -> Nat:
  0n

def main() -> Nat:
  0n
"""

main :: IO ()
main =
  testFile slash_definition_bend
    "definition names must not include '/'"
    $ \_ err -> do
      assert (err `has` "PARSE_ERROR")
      assert (err `has` "definition names cannot contain '/'")
