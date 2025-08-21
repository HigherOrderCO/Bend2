{-# LANGUAGE ViewPatterns #-}

-- Fork Desugaring
-- ===============
-- Removes all Frks from a Term, as follows:
--   fork L: A else: B (with ctx=[a,b,...])
--   --------------------------------------
--   &L{a0,a1} = a
--   &L{b0,b1} = b
--   ...
--   &L{A[a<-a0, b<-b0, ...], B[a<-a1,b<-b1, ...]}
-- That is, whenever a 'Frk L a b' constructor is found, we:
-- 1. Superpose each variable of the context (using a SupM with label L)
-- 2. Return a Sup of a and b, where the context on each side is entirely
--    replaced by the corresponding side of the forked variable

module Core.Adjust.DesugarFrks where

import Core.Bind
import Core.FreeVars
import Core.Show
import Core.Type
import qualified Data.Set as S

desugarFrks :: Book -> Int -> Term -> Term
desugarFrks book d term = desugarFrksGo book d [] term

desugarFrksGo :: Book -> Int -> [(Name, Int)] -> Term -> Term
desugarFrksGo book d ctx (Var n i)     = Var n i
desugarFrksGo book d ctx (Ref n i)     = Ref n i
desugarFrksGo book d ctx (Sub t)       = Sub (desugarFrksGo book d ctx t)
desugarFrksGo book d ctx (Fix n f)     = Fix n (\x -> desugarFrksGo book (d+1) ((n,d):ctx) (f x))
desugarFrksGo book d ctx (Let k t v f) = Let k (fmap (desugarFrksGo book d ctx) t) (desugarFrksGo book d ctx v) (\x -> desugarFrksGo book (d+1) ((k,d):ctx) (f x))
desugarFrksGo book d ctx (Use k v f)   = Use k (desugarFrksGo book d ctx v) (\x -> desugarFrksGo book (d+1) ((k,d):ctx) (f x))
desugarFrksGo book d ctx Set           = Set
desugarFrksGo book d ctx (Chk x t)     = Chk (desugarFrksGo book d ctx x) (desugarFrksGo book d ctx t)
desugarFrksGo book d ctx (Tst x)       = Tst (desugarFrksGo book d ctx x)
desugarFrksGo book d ctx Emp           = Emp
desugarFrksGo book d ctx EmpM          = EmpM
desugarFrksGo book d ctx Uni           = Uni
desugarFrksGo book d ctx One           = One
desugarFrksGo book d ctx (UniM f)      = UniM (desugarFrksGo book d ctx f)
desugarFrksGo book d ctx Bit           = Bit
desugarFrksGo book d ctx Bt0           = Bt0
desugarFrksGo book d ctx Bt1           = Bt1
desugarFrksGo book d ctx (BitM f t)    = BitM (desugarFrksGo book d ctx f) (desugarFrksGo book d ctx t)
desugarFrksGo book d ctx Nat           = Nat
desugarFrksGo book d ctx Zer           = Zer
desugarFrksGo book d ctx (Suc n)       = Suc (desugarFrksGo book d ctx n)
desugarFrksGo book d ctx (NatM z s)    = NatM (desugarFrksGo book d ctx z) (desugarFrksGo book d ctx s)
desugarFrksGo book d ctx (Lst t)       = Lst (desugarFrksGo book d ctx t)
desugarFrksGo book d ctx Nil           = Nil
desugarFrksGo book d ctx (Con h t)     = Con (desugarFrksGo book d ctx h) (desugarFrksGo book d ctx t)
desugarFrksGo book d ctx (LstM n c)    = LstM (desugarFrksGo book d ctx n) (desugarFrksGo book d ctx c)
desugarFrksGo book d ctx (Enu s)       = Enu s
desugarFrksGo book d ctx (Sym s)       = Sym s
desugarFrksGo book d ctx (EnuM c e)    = EnuM [(s, desugarFrksGo book d ctx t) | (s, t) <- c] (desugarFrksGo book d ctx e)
desugarFrksGo book d ctx (Sig a b)     = Sig (desugarFrksGo book d ctx a) (desugarFrksGo book d ctx b)
desugarFrksGo book d ctx (Tup a b)     = Tup (desugarFrksGo book d ctx a) (desugarFrksGo book d ctx b)
desugarFrksGo book d ctx (SigM f)      = SigM (desugarFrksGo book d ctx f)
desugarFrksGo book d ctx (All a b)     = All (desugarFrksGo book d ctx a) (desugarFrksGo book d ctx b)
desugarFrksGo book d ctx (Lam n t f)   = Lam n (fmap (desugarFrksGo book d ctx) t) (\x -> desugarFrksGo book (d+1) ((n,d):ctx) (f x))
desugarFrksGo book d ctx (App f x)     = App (desugarFrksGo book d ctx f) (desugarFrksGo book d ctx x)
desugarFrksGo book d ctx (Eql t a b)   = Eql (desugarFrksGo book d ctx t) (desugarFrksGo book d ctx a) (desugarFrksGo book d ctx b)
desugarFrksGo book d ctx Rfl           = Rfl
desugarFrksGo book d ctx (EqlM f)      = EqlM (desugarFrksGo book d ctx f)
desugarFrksGo book d ctx (Met i t x)   = Met i (desugarFrksGo book d ctx t) (map (desugarFrksGo book d ctx) x)
desugarFrksGo book d ctx Era           = Era
desugarFrksGo book d ctx (Sup l a b)   = Sup (desugarFrksGo book d ctx l) (desugarFrksGo book d ctx a) (desugarFrksGo book d ctx b)
desugarFrksGo book d ctx (SupM l f)    = SupM (desugarFrksGo book d ctx l) (desugarFrksGo book d ctx f)
desugarFrksGo book d ctx (Frk l a b)   = desugarFrk book d ctx l a b
desugarFrksGo book d ctx (Rwt e f)     = Rwt (desugarFrksGo book d ctx e) (desugarFrksGo book d ctx f)
desugarFrksGo book d ctx (Num t)       = Num t
desugarFrksGo book d ctx (Val v)       = Val v
desugarFrksGo book d ctx (Op2 o a b)   = Op2 o (desugarFrksGo book d ctx a) (desugarFrksGo book d ctx b)
desugarFrksGo book d ctx (Op1 o a)     = Op1 o (desugarFrksGo book d ctx a)
desugarFrksGo book d ctx (Pri p)       = Pri p
desugarFrksGo book d ctx (Log s x)     = Log (desugarFrksGo book d ctx s) (desugarFrksGo book d ctx x)
desugarFrksGo book d ctx (Loc s t)     = Loc s (desugarFrksGo book d ctx t)
desugarFrksGo book d ctx (Pat s m c)   = Pat (map (desugarFrksGo book d ctx) s) [(k, desugarFrksGo book d ctx v) | (k,v) <- m] [(p, desugarFrksGo book d (ctxCs p) f) | (p, f) <- c]
  where ctxCs  p = ctx ++ map (\(k,v) -> (k, d)) m ++ ctxPat p
        ctxPat p = map (\k -> (k, d)) (S.toList (S.unions (map (freeVars S.empty) p)))

desugarFrk :: Book -> Int -> [(Name, Int)] -> Term -> Term -> Term -> Term
desugarFrk book d ctx l a b = buildSupMs vars where
  vars =  shadowCtx (filter (\x -> fst x `S.member` free) (reverse ctx))
  free = case cut l of
    -- 'l' must be a non-superposed U64 so we can remove it from the forked vars as a (reasonable) optimization.
    Var n _ -> S.delete n (freeVars S.empty a `S.union` freeVars S.empty b)
    _       -> freeVars S.empty a `S.union` freeVars S.empty b
  -- Build nested SupM matches for each context variable
  buildSupMs :: [(Name, Int)] -> Term
  buildSupMs [] = Sup l a' b' where
    ls = [(n, Var (n++"0") 0) | (n, _) <- vars]
    rs = [(n, Var (n++"1") 0) | (n, _) <- vars]
    a' = bindVarByNameMany ls (desugarFrksGo book d ctx a)
    b' = bindVarByNameMany rs (desugarFrksGo book d ctx b)
  -- For each variable, create a SupM that binds the superposed versions
  buildSupMs ((n,d):rest) =
    App (SupM l $
    Lam (n++"0") Nothing $ \_ ->
    Lam (n++"1") Nothing $ \_ ->
    buildSupMs rest) (Var n d)
  -- Removes repeated (shadowed) vars from the context
  shadowCtx ((n,d):ctx) =
    if n `elem` (map fst ctx)
      then shadowCtx ctx
      else (n,d) : shadowCtx ctx
  shadowCtx [] = []
