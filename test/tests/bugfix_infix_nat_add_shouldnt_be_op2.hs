{-# LANGUAGE MultilineStrings #-}

import Test

-- fixed in commit 1d6d800fc0ed1873fc91b84111ab1a41d2e2ba90
--
-- note: (a+b) for Nats requires Nat/add in context
--
-- bug description:
-- (a+b) == add(a,b) can't be proven because (a+b) parses as (Op2 ADD)
--
--   ✗ f
--   Mismatch:
--   - Goal: Num
--   - Type: Nat
--   Context:
--   - a : Nat
--   - b : Nat
--   Location: (line 17, column 3)
--   17 |   a+b

main_bend :: String
main_bend = """
def add_x_y (a:Nat, b:Nat) -> Nat{(a+b) == Nat/add(a,b)}:
  match a:
    case 0n:
      finally
    case 1n + p:
      finally
"""

nat_add_bend :: String
nat_add_bend = """
def add(a:Nat, b:Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n+p:
      1n+add(p,b)
"""

main :: IO ()
main =
  test "bend main.bend"
    [ ("main.bend", main_bend)
    , ("Nat/add.bend", nat_add_bend)
    ]
    "Nat/add should back application of '+'"
    $ \_ err -> assert (err == "")
