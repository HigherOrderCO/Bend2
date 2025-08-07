{-# LANGUAGE MultilineStrings #-}

import Test

-- fixed in commit f10831ebfc0c709b05a038149f7067b562f10f36
--
-- bug description:
-- Eta reducing nested pattern matches with lambda variables in reversed / wrong order does not work


eta_reduce_nested_pats :: String
eta_reduce_nested_pats = """
type A:
  case B{}:
    x: Nat
  case C{}:
    y: Unit

def f1(s: Char[], b: Bool, c: Nat) -> Unit:
  if b:
    match s:
      case []:
        ()
      case h <> t:
        ()
  else:
      match c:
        case 0n:
          ()
        case 1n+p:
          ()

def f2_aux(b : Unit) -> Unit:
  match b:
    case ():
      ()

def f2(a : Unit) -> Unit:
  b : Unit = ~a { (): () }
  f2_aux(b)


def f3(s: A, b: Bool) -> Unit:
  if b:
    match s:
      case B{x}:
        ()
      case C{y}:
        ()
  else:
    ()

"""

main :: IO ()
main = testFileChecks eta_reduce_nested_pats
