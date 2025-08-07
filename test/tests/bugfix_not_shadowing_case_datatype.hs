{-# LANGUAGE MultilineStrings #-}

-- fixed in commit (BenGen-align) 22927b73254c582acee6fba1a1c555bc5e5650e6

-- bug description:
-- shadowing of a variable of custom type by case declaration is not working, giving wrong result
--
-- ✓ Nats
-- ✓ pred
-- ✓ main
--
-- S{Z{}}

import Test

not_shadowing_case_datatype :: String
not_shadowing_case_datatype = """
type Nats: 
  case Z{}:
  case S{}: pred: Nats

def pred(n: Nats) -> Nats:
  match n:
    case Z{} : Z{}
    case S{n}: n

def main() -> Nats:
  pred(S{Z{}})
"""

main :: IO ()
main = testFile not_shadowing_case_datatype
  "Result should be Z{}, not S{Z{}} if shadowing of n works in pred" (\out err -> do
    assert (not (out `has` "S{Z{}}"))
    assert (out `has` "Z{}")
    assert (err == "")
    )

