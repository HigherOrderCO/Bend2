{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
def main() -> Nat:
  Nat/add::inc(0n)
"""

nat_add_bend :: String
nat_add_bend = """
def add(n: Nat, m: Nat) -> Nat:
  inc(n, m)

def inc(n: Nat, m: Nat) -> Nat:
  m
"""

main :: IO ()
main =
  test "bend main.bend"
    [ ("main.bend", main_bend)
    , ("Nat/add.bend", nat_add_bend)
    ]
    "private helpers cannot be imported from other files"
    $ \_ err -> do
      assert (err /= "")
      assert (err `has` "ImportError")
      assert (err `has` "is private to 'Nat/add'")
