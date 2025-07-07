{-./Type.hs-}

module Core.Rewrite where

import System.IO.Unsafe
import Data.IORef
import Data.Bits
import GHC.Float (castDoubleToWord64, castWord64ToDouble)

import Core.Equal
import Core.Type
import Core.WHNF

import Debug.Trace

-- Rewrite
-- =======

rewrite :: Int -> Int -> Book -> Term -> Term -> Term -> Term
rewrite lv d book old neo val
  | equal d book old val = neo
  | otherwise            = rewriteGo lv d book old neo $ whnf Soft book val
  -- | equal d book old val = trace ("eq " ++ show old ++ " → " ++ show neo ++ " |" ++ show val ++ " → " ++ show (whnf 2 d book val)) $ neo
  -- | otherwise            = trace ("rw " ++ show old ++ " → " ++ show neo ++ " |" ++ show val ++ " → " ++ show (whnf 2 d book val))
                         -- $ rewriteGo lv d book old neo $ whnf 2 d book val

-- Recursively rewrites occurrences of 'old' with 'neo' in 'val'
rewriteGo :: Int -> Int -> Book -> Term -> Term -> Term -> Term
rewriteGo lv d book old neo val = case val of
  Var k i    -> Var k i
  Ref k      -> Ref k
  Sub t      -> t
  Fix k f    -> Fix k (\x -> rewrite lv d book old neo (f x))
  Let v f    -> Let (rewrite lv d book old neo v) (rewrite lv d book old neo f)
  Set        -> Set
  Chk x t    -> Chk (rewrite lv d book old neo x) (rewrite lv d book old neo t)
  Emp        -> Emp
  EmpM x     -> EmpM (rewrite lv d book old neo x)
  Uni        -> Uni
  One        -> One
  UniM x f   -> UniM (rewrite lv d book old neo x) (rewrite lv d book old neo f)
  Bit        -> Bit
  Bt0        -> Bt0
  Bt1        -> Bt1
  BitM x f t -> BitM (rewrite lv d book old neo x) (rewrite lv d book old neo f) (rewrite lv d book old neo t)
  Nat        -> Nat
  Zer        -> Zer
  Suc n      -> Suc (rewrite lv d book old neo n)
  NatM x z s -> NatM (rewrite lv d book old neo x) (rewrite lv d book old neo z) (rewrite lv d book old neo s)
  Lst t      -> Lst (rewrite lv d book old neo t)
  Nil        -> Nil
  Con h t    -> Con (rewrite lv d book old neo h) (rewrite lv d book old neo t)
  LstM x n c -> LstM (rewrite lv d book old neo x) (rewrite lv d book old neo n) (rewrite lv d book old neo c)
  Enu s      -> Enu s
  Sym s      -> Sym s
  EnuM x c e -> EnuM (rewrite lv d book old neo x) (map (\(s,t) -> (s, rewrite lv d book old neo t)) c) (rewrite lv d book old neo e)
  Num t      -> Num t
  Val v      -> Val v
  Op2 o a b  -> Op2 o (rewrite lv d book old neo a) (rewrite lv d book old neo b)
  Op1 o a    -> Op1 o (rewrite lv d book old neo a)
  Sig a b    -> Sig (rewrite lv d book old neo a) (rewrite lv d book old neo b)
  Tup a b    -> Tup (rewrite lv d book old neo a) (rewrite lv d book old neo b)
  SigM x f   -> SigM (rewrite lv d book old neo x) (rewrite lv d book old neo f)
  All a b    -> All (rewrite lv d book old neo a) (rewrite lv d book old neo b)
  Lam k f    -> Lam k (\v -> rewrite lv d book old neo (f v))
  App f x    -> foldl (\ f x -> App f (rewrite lv d book old neo x)) fn xs
          where (fn,xs) = collectApps (App f x) []
  Eql t a b  -> Eql (rewrite lv d book old neo t) (rewrite lv d book old neo a) (rewrite lv d book old neo b)
  Rfl        -> Rfl
  EqlM x f   -> EqlM (rewrite lv d book old neo x) (rewrite lv d book old neo f)
  Met i t a  -> Met i (rewrite lv d book old neo t) (map (rewrite lv d book old neo) a)
  Ind t      -> Ind (rewrite lv d book old neo t)
  Frz t      -> Frz (rewrite lv d book old neo t)
  Era        -> Era
  Sup l a b  -> Sup l (rewrite lv d book old neo a) (rewrite lv d book old neo b)
  SupM x l f -> SupM (rewrite lv d book old neo x) (rewrite lv d book old neo l) (rewrite lv d book old neo f)
  Frk l a b  -> Frk (rewrite lv d book old neo l) (rewrite lv d book old neo a) (rewrite lv d book old neo b)
  Loc s t    -> Loc s (rewrite lv d book old neo t)
  Rwt a b x  -> Rwt (rewrite lv d book old neo a) (rewrite lv d book old neo b) (rewrite lv d book old neo x)
  Log s x    -> Log (rewrite lv d book old neo s) (rewrite lv d book old neo x)
  Pri p      -> Pri p
  Pat t m c  -> Pat (map (rewrite lv d book old neo) t) (map (\(k,v) -> (k, rewrite lv d book old neo v)) m) (map (\(ps,v) -> (map (rewrite lv d book old neo) ps, rewrite lv d book old neo v)) c)

rewriteCtx :: Int -> Int -> Book -> Term -> Term -> Ctx -> Ctx
rewriteCtx lv d book old neo (Ctx ctx) = Ctx (map rewriteAnn ctx)
  where rewriteAnn (k,v,t) = (k, v, rewrite lv d book old neo t)
