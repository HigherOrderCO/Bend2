{-./Type.hs-}

module Core.Bind where

import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Debug.Trace

import Core.Type

bind :: Term -> Term
bind term = bound where
  bound = binder 0 term [] M.empty

binder :: Int -> Term -> [Term] -> M.Map Name Term -> Term
binder lv term ctx vars = case term of
  Var k i    -> case M.lookup k vars of { Just t -> t ; Nothing -> Ref k }
  Ref k      -> Ref k
  Sub t      -> t
  Let v f    -> Let (binder lv v ctx vars) (binder lv f ctx vars)
  Fix k f    -> Fix k (\x -> binder (lv+1) (f (Sub x)) (ctx++[x]) (M.insert k x vars))
  Set        -> Set
  Chk x t    -> Chk (binder lv x ctx vars) (binder lv t ctx vars)
  Emp        -> Emp
  EmpM x     -> EmpM (binder lv x ctx vars)
  Uni        -> Uni
  One        -> One
  UniM x f   -> UniM (binder lv x ctx vars) (binder lv f ctx vars)
  Bit        -> Bit
  Bt0        -> Bt0
  Bt1        -> Bt1
  BitM x f t -> BitM (binder lv x ctx vars) (binder lv f ctx vars) (binder lv t ctx vars)
  Nat        -> Nat
  Zer        -> Zer
  Suc n      -> Suc (binder lv n ctx vars)
  NatM x z s -> NatM (binder lv x ctx vars) (binder lv z ctx vars) (binder lv s ctx vars)
  Lst t      -> Lst (binder lv t ctx vars)
  Nil        -> Nil
  Con h t    -> Con (binder lv h ctx vars) (binder lv t ctx vars)
  LstM x n c -> LstM (binder lv x ctx vars) (binder lv n ctx vars) (binder lv c ctx vars)
  Enu s      -> Enu s
  Sym s      -> Sym s
  EnuM x c e -> EnuM (binder lv x ctx vars) (map (\(s, t) -> (s, binder lv t ctx vars)) c) (binder lv e ctx vars)
  Sig a b    -> Sig (binder lv a ctx vars) (binder lv b ctx vars)
  Tup a b    -> Tup (binder lv a ctx vars) (binder lv b ctx vars)
  SigM x f   -> SigM (binder lv x ctx vars) (binder lv f ctx vars)
  All a b    -> All (binder lv a ctx vars) (binder lv b ctx vars)
  Lam k f    -> Lam k (\x -> binder (lv+1) (f (Sub x)) (ctx++[x]) (M.insert k x vars))
  App f x    -> App (binder lv f ctx vars) (binder lv x ctx vars)
  Eql t a b  -> Eql (binder lv t ctx vars) (binder lv a ctx vars) (binder lv b ctx vars)
  Rfl        -> Rfl
  EqlM x f   -> EqlM (binder lv x ctx vars) (binder lv f ctx vars)
  Ind t      -> Ind (binder lv t ctx vars)
  Frz t      -> Frz (binder lv t ctx vars)
  Loc s t    -> Loc s (binder lv t ctx vars)
  Rwt a b x  -> Rwt (binder lv a ctx vars) (binder lv b ctx vars) (binder lv x ctx vars)
  Era        -> Era
  Sup l a b  -> Sup l (binder lv a ctx vars) (binder lv b ctx vars)
  Num t      -> Num t
  Val v      -> Val v
  Op2 o a b  -> Op2 o (binder lv a ctx vars) (binder lv b ctx vars)
  Op1 o a    -> Op1 o (binder lv a ctx vars)
  Pri p      -> Pri p
  Met k t c  -> Met k (binder lv t ctx vars) (map (\x -> binder lv x ctx vars) c)
  Pat s m c  -> error "not-supported"
