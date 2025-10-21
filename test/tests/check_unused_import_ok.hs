{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
import Tests/answer as Answer

def main : Nat =
  0n
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
    "unused explicit import should succeed"
    $ \_ err -> assert (err == "")
