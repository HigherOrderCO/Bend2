{-./Type.hs-}

module Core.Bind where

import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Debug.Trace

import Core.Type
import Core.FreeVars

bind :: Term -> Term
bind term = bound where
  bound = binder 0 term [] M.empty

binder :: Int -> Term -> [Term] -> M.Map Name Term -> Term
binder lv term ctx vars = case term of
  Var k i     -> case M.lookup k vars of { Just t -> t ; Nothing -> Ref k 1}
  Ref k i     -> Ref k i
  Sub t       -> t
  Let k t v f -> Let k (fmap (\u -> binder lv u ctx vars) t) (binder lv v ctx vars) (\x -> binder lv (f (Sub x)) (ctx++[x]) (M.insert k x vars))
  Use k v f   -> Use k (binder lv v ctx vars) (\x -> binder lv (f (Sub x)) (ctx++[x]) (M.insert k x vars))
  Fix k f     -> Fix k (\x -> binder (lv+1) (f (Sub x)) (ctx++[x]) (M.insert k x vars))
  Set         -> Set
  Chk x t     -> Chk (binder lv x ctx vars) (binder lv t ctx vars)
  Emp         -> Emp
  EmpM        -> EmpM
  Uni         -> Uni
  One         -> One
  UniM f      -> UniM (binder lv f ctx vars)
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
  EqlM f      -> EqlM (binder lv f ctx vars)
  Rwt e f     -> Rwt (binder lv e ctx vars) (binder lv f ctx vars)
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

-- Generic bind function that takes a predicate to match variables
bindVar :: (Name -> Int -> Bool) -> Term -> Term -> Term
bindVar match val term = go term where
  go term = case term of
    Var k i     -> if match k i then val else term
    Ref k i     -> Ref k i
    Sub t       -> t
    Fix k f     -> Fix k (\x -> go (f (Sub x)))
    Let k t v f -> Let k (fmap go t) (go v) (\x -> go (f (Sub x)))
    Use k v f   -> Use k (go v) (\x -> go (f (Sub x)))
    Set         -> Set
    Chk x t     -> Chk (go x) (go t)
    Emp         -> Emp
    EmpM        -> EmpM
    Uni         -> Uni
    One         -> One
    UniM f      -> UniM (go f)
    Bit         -> Bit
    Bt0         -> Bt0
    Bt1         -> Bt1
    BitM f t    -> BitM (go f) (go t)
    Nat         -> Nat
    Zer         -> Zer
    Suc n       -> Suc (go n)
    NatM z s    -> NatM (go z) (go s)
    Lst t       -> Lst (go t)
    Nil         -> Nil
    Con h t     -> Con (go h) (go t)
    LstM n c    -> LstM (go n) (go c)
    Enu s       -> Enu s
    Sym s       -> Sym s
    EnuM c e    -> EnuM [(s, go t) | (s, t) <- c] (go e)
    Sig a b     -> Sig (go a) (go b)
    Tup a b     -> Tup (go a) (go b)
    SigM f      -> SigM (go f)
    All a b     -> All (go a) (go b)
    Lam k t f   -> Lam k (fmap go t) (\x -> go (f (Sub x)))
    App f x     -> App (go f) (go x)
    Eql t a b   -> Eql (go t) (go a) (go b)
    Rfl         -> Rfl
    EqlM f      -> EqlM (go f)
    Rwt e f     -> Rwt (go e) (go f)
    Met n t x   -> Met n (go t) (map go x)
    Era         -> Era
    Sup l a b   -> Sup (go l) (go a) (go b)
    SupM l f    -> SupM (go l) (go f)
    Frk l a b   -> Frk (go l) (go a) (go b)
    Loc s t     -> Loc s (go t)
    Log s x     -> Log (go s) (go x)
    Pri p       -> Pri p
    Num t       -> Num t
    Val v       -> Val v
    Op2 o a b   -> Op2 o (go a) (go b)
    Op1 o a     -> Op1 o (go a)
    Pat s m c   -> Pat (map go s) [(k, go v) | (k, v) <- m] [(ps, go b) | (ps, b) <- c]

-- Bind by index
bindVarByIndex :: Int -> Term -> Term -> Term
bindVarByIndex i = bindVar (\_ i' -> i == i')

-- Bind by name
bindVarByName :: Name -> Term -> Term -> Term
bindVarByName name = bindVar (\k _ -> k == name)

-- Helper to substitute multiple variables at once
bindVarByNameMany :: [(Name, Term)] -> Term -> Term
bindVarByNameMany subs term = foldr (\ (n,v) t -> bindVarByName n v t) term subs
