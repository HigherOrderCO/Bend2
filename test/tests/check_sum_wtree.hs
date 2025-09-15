{-# LANGUAGE MultilineStrings #-}

import Test

sum_wtree_bend :: String
sum_wtree_bend = """
def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + add(p, b)

type W(A: Set, B: A -> Set):
  case @Sup:
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
    case @Sup{x,f}:
      F(x, λy. wfold(A,B,P,f(y),F))

type WTreeTag<A: Set>:
  case @WLeaf:
    value: A
  case @WNode:

def WTreeRec(tag: WTreeTag(Nat)) -> Set:
  match tag:
    case @WLeaf{value}:
      return Empty
    case @WNode:
      return enum{&lft, &rgt}

def WTree : Set =
  W(WTreeTag(Nat), WTreeRec)

def WLeaf(n: Nat) -> WTree:
  return @Sup{@WLeaf{n}, λe. absurd e}

def WNode(l: WTree, r: WTree) -> WTree:
  return @Sup{@WNode{}, λi. match i: case &lft: l case &rgt: r  }

def sum_wtree(w: WTree) -> Nat:
  match w:
    case @Sup{@WLeaf{value},f}:
      value
    case @Sup{@WNode{},f}:
      a = f(&lft)
      b = f(&rgt)
      return add(sum_wtree(a), sum_wtree(b))

def sum_wtree_fold(w: WTree) -> Nat:
  wfold<WTreeTag(Nat), WTreeRec, Nat>(w,
    lambda tag f.
    match tag:
      case @WLeaf{value}:
        value
      case @WNode:
        add(f(&lft), f(&rgt)))

assert 5n == sum_wtree(WLeaf(5n)) : Nat
assert 7n == sum_wtree(WNode(WLeaf(3n), WLeaf(4n))) : Nat
assert 10n == sum_wtree(WNode(WNode(WLeaf(2n), WLeaf(3n)), WLeaf(5n))) : Nat
assert 5n == sum_wtree_fold(WLeaf(5n)) : Nat
assert 7n == sum_wtree_fold(WNode(WLeaf(3n), WLeaf(4n))) : Nat
"""

main :: IO ()
main = testFileChecks sum_wtree_bend
