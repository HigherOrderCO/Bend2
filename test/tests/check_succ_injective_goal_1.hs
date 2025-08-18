{-# LANGUAGE MultilineStrings #-}

import Test

succ_injective_goal_1_bend :: String
succ_injective_goal_1_bend = """
def succ_injective(n: Nat, m: Nat, e: Nat{1n+n==1n+m}) -> Nat{n==m}:
  match n m e:
    case 0n 0n e:
      {==}
    case 1n+n 0n e:
      ()
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
main = testFileGoal succ_injective_goal_1_bend "Nat{1n+n$p==0n}" []
