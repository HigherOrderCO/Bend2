{-# LANGUAGE MultilineStrings #-}

import Test

is_even_equivalence_bend :: String
is_even_equivalence_bend = """
def neg(x: Bool) -> Bool:
  if x:
    False
  else:
    True

def double_neg_identity(x: Bool) -> Bool{neg(neg(x)) == x}:
  if x:
    {==}
  else:
    {==}

def is_even_a(n: Nat) -> Bool:
  match n:
    case 0n:
      True
    case 1n:
      False
    case 2n + p:
      is_even_a(p)

def is_even_b(n: Nat) -> Bool:
  match n:
    case 0n:
      True
    case 1n + p:
      neg(is_even_b(p))

def is_even_equivalence(n: Nat) -> Bool{is_even_a(n) == is_even_b(n)}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n + p:
      rewrite double_neg_identity(is_even_b(p))
      is_even_equivalence(p)
"""

main :: IO ()
main = testFileChecks is_even_equivalence_bend