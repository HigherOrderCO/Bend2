{-# LANGUAGE MultilineStrings #-}

import Test

succ_injective_bend :: String
succ_injective_bend = """
def succ_injective(n: Nat, m: Nat, e: (1n+n)==(1n+m) :: Nat) -> n==m :: Nat:
  match n m e:
    case 0n 0n e:
      {==}
    case 1n+n 0n e:
      absurd e
    case 0n 1n+m e:
      absurd e
    case 1n+n 1n+m e:
      match e:
        case 0n:
          ()
        case 1n+e:
          e
"""

main :: IO ()
main = testFileChecks succ_injective_bend