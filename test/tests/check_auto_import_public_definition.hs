{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
def main : Nat =
  Tests/answer
"""

answer_bend :: String
answer_bend = """
def answer : Nat =
  42n
"""

main :: IO ()
main =
  test "bend main.bend"
    [ ("main.bend", main_bend)
    , ("Tests/answer.bend", answer_bend)
    ]
    "auto-import loads public definition without explicit import"
    $ \_ err -> assert (err == "")
