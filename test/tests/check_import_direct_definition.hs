{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
import Tests/answer as ans

def main : Nat =
  ans

assert 42n == ans : Nat
assert 42n == main : Nat
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
    "importing a direct definition via FQN succeeds"
    $ \_ err -> assert (err == "")
