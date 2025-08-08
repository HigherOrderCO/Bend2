{-# LANGUAGE MultilineStrings #-}

import Test

w_bend :: String
w_bend = """
type W(A: Set, B: A -> Set):
  case Sup{}:
    x: A
    f: B(x) -> W(A,B)

def wfold
  ( A: Set
  , B: A -> Set
  , P: Set
  , w: W(A,B)
  , F: all x:A k:(B(x) -> P) . P
  ) -> P:
  match w:
    case Sup{x,f}:
      F(x, λy. wfold(A,B,P,f(y),F))

type WTreeTag<A: Set>:
  case WLeaf{}:
    value: A
  case WNode{}:

type Direction:
  case Lft{}:
  case Rgt{}:

def WTreeRec(tag: WTreeTag(Nat)) -> Set:
  match tag:
    case WLeaf{value}:
      return Empty
    case WNode:
      return Direction 

def WTree : Set =
  W(WTreeTag(Nat), WTreeRec)

def WLeaf(n: Nat) -> WTree:
  return Sup{WLeaf{n}, λe. absurd e}

def WNode(l: WTree, r: WTree) -> WTree:
  return Sup{WNode{}, λi. match i: case Lft: l case Rgt: r  }
"""

main :: IO ()
main = testFileChecks w_bend
