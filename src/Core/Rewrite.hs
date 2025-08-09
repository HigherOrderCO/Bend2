{-./Type.hs-}
{-./WHNF.hs-}
{-./Equal.hs-}

module Core.Rewrite where

import System.IO.Unsafe
import Data.IORef
import Data.Bits
import GHC.Float (castDoubleToWord64, castWord64ToDouble)

import Core.Equal
import Core.Type
import Core.Show
import Core.WHNF

import Debug.Trace

-- Rewrite
-- =======

rewrite :: Int -> Book -> Term -> Term -> Term -> Term
rewrite d book old neo val
  | equal d book old val = neo
  | otherwise            = rewriteGo d book old neo $ whnf book val

-- Recursively rewrites occurrences of 'old' with 'neo' in 'val'
rewriteGo :: Int -> Book -> Term -> Term -> Term -> Term
rewriteGo d book old neo val =
  case val of
    Var k i     -> Var k i
    Ref k i     -> Ref k i
    Sub t       -> t
    Fix k f     -> Fix k (\x -> rewrite d book old neo (f x))
    Let k t v f -> Let k (fmap (rewrite d book old neo) t) (rewrite d book old neo v) (\x -> rewrite d book old neo (f x))
    Use k v f   -> Use k (rewrite d book old neo v) (\x -> rewrite d book old neo (f x))
    Set         -> Set
    Chk x t     -> Chk (rewrite d book old neo x) (rewrite d book old neo t)
    Emp         -> Emp
    EmpM        -> EmpM
    Uni         -> Uni
    One         -> One
    UniM f      -> UniM (rewrite d book old neo f)
    Bit         -> Bit
    Bt0         -> Bt0
    Bt1         -> Bt1
    BitM f t    -> BitM (rewrite d book old neo f) (rewrite d book old neo t)
    Nat         -> Nat
    Zer         -> Zer
    Suc n       -> Suc (rewrite d book old neo n)
    NatM z s    -> NatM (rewrite d book old neo z) (rewrite d book old neo s)
    Lst t       -> Lst (rewrite d book old neo t)
    Nil         -> Nil
    Con h t     -> Con (rewrite d book old neo h) (rewrite d book old neo t)
    LstM n c    -> LstM (rewrite d book old neo n) (rewrite d book old neo c)
    ADT n ps    -> ADT n (map (rewrite d book old neo) ps)
    Ctr n vs    -> Ctr n (map (rewrite d book old neo) vs)
    ADTM t cs df -> ADTM t (map (\(n,c) -> (n, rewrite d book old neo c)) cs) (fmap (rewrite d book old neo) df)
    Num t       -> Num t
    Val v       -> Val v
    Op2 o a b   -> Op2 o (rewrite d book old neo a) (rewrite d book old neo b)
    Op1 o a     -> Op1 o (rewrite d book old neo a)
    Sig a b     -> Sig (rewrite d book old neo a) (rewrite d book old neo b)
    Tup a b     -> Tup (rewrite d book old neo a) (rewrite d book old neo b)
    SigM f      -> SigM (rewrite d book old neo f)
    All a b     -> All (rewrite d book old neo a) (rewrite d book old neo b)
    Lam k t f   -> Lam k (fmap (rewrite d book old neo) t) (\v -> rewrite d book old neo (f v))
    App f x     -> foldl (\ f x -> App f (rewrite d book old neo x)) fn xs
      where (fn,xs) = collectApps (App f x) []
    Eql t a b   -> Eql (rewrite d book old neo t) (rewrite d book old neo a) (rewrite d book old neo b)
    Rfl         -> Rfl
    EqlM f      -> EqlM (rewrite d book old neo f)
    Rwt e f     -> Rwt (rewrite d book old neo e) (rewrite d book old neo f)
    Met i t a   -> Met i (rewrite d book old neo t) (map (rewrite d book old neo) a)
    Era         -> Era
    Sup l a b   -> Sup l (rewrite d book old neo a) (rewrite d book old neo b)
    SupM l f    -> SupM (rewrite d book old neo l) (rewrite d book old neo f)
    Frk l a b   -> Frk (rewrite d book old neo l) (rewrite d book old neo a) (rewrite d book old neo b)
    Loc s t     -> Loc s (rewrite d book old neo t)
    Log s x     -> Log (rewrite d book old neo s) (rewrite d book old neo x)
    Pri p       -> Pri p
    Pat t m c   -> Pat (map (rewrite d book old neo) t) (map (\(k,v) -> (k, rewrite d book old neo v)) m) (map (\(ps,v) -> (map (rewrite d book old neo) ps, rewrite d book old neo v)) c)

rewriteCtx :: Int -> Book -> Term -> Term -> Ctx -> Ctx
rewriteCtx d book old neo (Ctx ctx) = Ctx (map rewriteAnn ctx)
  where rewriteAnn (k,v,t) = (k, v, rewrite d book old neo t)














-- this repository has been just refactored using AI. check Type.hs to see the
-- refactor instructions. sadly, the comm proof on examples/main.bend is not
-- checking anymore. when we have the goal `1n+add(ap,b) == add(b,1n+ap) : Nat`,
-- and we rewrite it with `e0 : add(ap,b) == add(b,ap) : Nat`, the goal is
-- updated to `1n+add(b,ap) == add(b,ap) : Nat`, which is clearly not correct:
-- the right side is NOT equal to `add(ap,b)`, so it should NOT be rewritten to
-- `add(b,ap)`.  seems like, on the refactor, something broke how rewrite or
-- equality works. investigate the old and new files, and spot the divergence.
-- explain the culprit below, in plain English.





















