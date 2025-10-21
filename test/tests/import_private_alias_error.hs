{-# LANGUAGE MultilineStrings #-}

import Test

main_bend :: String
main_bend = """
import Nat/add as NatAdd

def main : Nat =
  NatAdd/inc(0n)
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
    "alias should not expose private helpers"
    $ \_ err -> do
      assert (err /= "")
      assert (err `has` "ImportError")
      assert (err `has` "unable to locate module 'Nat/add/inc'")
