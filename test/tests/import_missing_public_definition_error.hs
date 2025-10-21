{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
def main : Nat =
  Tests/answer::missing
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
    "referencing missing public definition should fail"
    $ \_ err -> do
      assert (err /= "")
      assert (err `has` "'Tests/answer::missing' is private to 'Tests/answer'")
