{-# LANGUAGE MultilineStrings #-}

import Test

vecind_goal_0_bend :: String
vecind_goal_0_bend = """
type Vec<A: Set>(N: Nat) -> Set:
  case Nil{}:
    e: N == 0n :: Nat
  case Cons{}:
    n: Nat
    h: A
    t: Vec(A,n)
    e: N == (1n+n) :: Nat

def VecInd
  ( A: Set
  , P: all n:Nat xs:Vec(A,n). Set
  , N: P(0n,Nil{{==}})
  , C: all s:Nat x:A xs:Vec(A,s) p:P(s,xs). P(1n+s,Cons{s,x,xs,{==}})
  , n: Nat
  , x: Vec(A,n)
  ) -> P(n,x):
  match x:
    case Nil{{==}}:
      ()
    case Cons{n,h,t,{==}}:
      C(n,h,t,VecInd(A,P,N,C,n,t))
"""

main :: IO ()
main = testFileGoal vecind_goal_0_bend "P(0n,Nil{{==}})" []
