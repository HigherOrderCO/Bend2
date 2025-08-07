{-# LANGUAGE MultilineStrings #-}

import Test

-- bug description:
-- see https://github.com/HigherOrderCO/Bend2/issues/16
--

nested_pat_match_same_scrutinee :: String
nested_pat_match_same_scrutinee = """
type Term:
  case A{}:
  case B{}:

def f(a: Term) -> Unit:
  match a:
    case A{}: ()
    case a:
      match a:
        case A{}: ()
        case B{}: ()

"""

main :: IO ()
main = testFileChecks nested_pat_match_same_scrutinee
