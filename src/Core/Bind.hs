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
  Var k i     -> case M.lookup k vars of { Just t -> t ; Nothing -> Ref k }
  Ref k       -> Ref k
  Sub t       -> t
  Let k t v f -> Let k (fmap (\u -> binder lv u ctx vars) t) (binder lv v ctx vars) (\x -> binder lv (f (Sub x)) (ctx++[x]) (M.insert k x vars))
  Fix k f     -> Fix k (\x -> binder (lv+1) (f (Sub x)) (ctx++[x]) (M.insert k x vars))
  Set         -> Set
  Chk x t     -> Chk (binder lv x ctx vars) (binder lv t ctx vars)
  Emp         -> Emp
  EmpM        -> EmpM
  Uni         -> Uni
  One         -> One
  UniM x f    -> UniM (binder lv x ctx vars) (binder lv f ctx vars)
  Bit         -> Bit
  Bt0         -> Bt0
  Bt1         -> Bt1
  BitM f t    -> BitM (binder lv f ctx vars) (binder lv t ctx vars)
  Nat         -> Nat
  Zer         -> Zer
  Suc n       -> Suc (binder lv n ctx vars)
  NatM z s    -> NatM (binder lv z ctx vars) (binder lv s ctx vars)
  Lst t       -> Lst (binder lv t ctx vars)
  Nil         -> Nil
  Con h t     -> Con (binder lv h ctx vars) (binder lv t ctx vars)
  LstM n c    -> LstM (binder lv n ctx vars) (binder lv c ctx vars)
  Enu s       -> Enu s
  Sym s       -> Sym s
  EnuM c e    -> EnuM (map (\(s, t) -> (s, binder lv t ctx vars)) c) (binder lv e ctx vars)
  Sig a b     -> Sig (binder lv a ctx vars) (binder lv b ctx vars)
  Tup a b     -> Tup (binder lv a ctx vars) (binder lv b ctx vars)
  SigM f      -> SigM (binder lv f ctx vars)
  All a b     -> All (binder lv a ctx vars) (binder lv b ctx vars)
  Lam k t f   -> Lam k (fmap (\t -> binder lv t ctx vars) t) (\x -> binder (lv+1) (f (Sub x)) (ctx++[x]) (M.insert k x vars))
  App f x     -> App (binder lv f ctx vars) (binder lv x ctx vars)
  Eql t a b   -> Eql (binder lv t ctx vars) (binder lv a ctx vars) (binder lv b ctx vars)
  Rfl         -> Rfl
  Rwt e g f   -> Rwt (binder lv e ctx vars) (binder lv g ctx vars) (binder lv f ctx vars)
  Loc s t     -> Loc s (binder lv t ctx vars)
  Era         -> Era
  Sup l a b   -> Sup (binder lv l ctx vars) (binder lv a ctx vars) (binder lv b ctx vars)
  SupM l f    -> SupM (binder lv l ctx vars) (binder lv f ctx vars)
  Frk l a b   -> Frk (binder lv l ctx vars) (binder lv a ctx vars) (binder lv b ctx vars)
  Num t       -> Num t
  Val v       -> Val v
  Op2 o a b   -> Op2 o (binder lv a ctx vars) (binder lv b ctx vars)
  Op1 o a     -> Op1 o (binder lv a ctx vars)
  Pri p       -> Pri p
  Log s x     -> Log (binder lv s ctx vars) (binder lv x ctx vars)
  Met k t c   -> Met k (binder lv t ctx vars) (map (\x -> binder lv x ctx vars) c)
  Pat s m c   ->
    -- Since Pat doesn't bind with HOAS, keep as Var
    let s'     = map (\x -> binder lv x ctx vars) s
        m'     = map (\(k,x) -> (k, binder lv x ctx vars)) m
        c'     = map (\(p,x) -> (p, binder lv x (ctx ++ map v mvar ++ map v (pvar p)) (M.union (M.fromList (map kv (mvar ++ pvar p))) vars))) c
        mvar   = map fst m
        pvar p = S.toList (S.unions (map (freeVars S.empty) p))
        kv nam = (nam, Var nam 0)
        v nam  = Var nam 0
    in Pat s' m' c'
