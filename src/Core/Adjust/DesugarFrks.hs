{-./../Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Adjust.DesugarFrks where

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

import Core.Bind
import Core.FreeVars
import Core.Show
import Core.Type
import qualified Data.Set as S

desugarFrks :: Book -> Int -> Term -> Term
desugarFrks book d term = go d [] term where

  go :: Int -> [(Name, Int)] -> Term -> Term
  go d ctx (Var k i)     = Var k i
  go d ctx (Ref n i)     = Ref n i
  go d ctx (Sub t)       = Sub (go d ctx t)
  go d ctx (Fix n f)     = Fix n (\x -> go (d+1) ((n,d):ctx) (f x))
  go d ctx (Let k t v f) = Let k (fmap (go d ctx) t) (go d ctx v) (\x -> go (d+1) ((k,d):ctx) (f x))
  go d ctx (Use k v f)   = Use k (go d ctx v) (\x -> go (d+1) ((k,d):ctx) (f x))
  go d ctx Set           = Set
  go d ctx (Chk x t)     = Chk (go d ctx x) (go d ctx t)
  go d ctx Emp           = Emp
  go d ctx EmpM          = EmpM
  go d ctx Uni           = Uni
  go d ctx One           = One
  go d ctx (UniM f)      = UniM (go d ctx f)
  go d ctx Bit           = Bit
  go d ctx Bt0           = Bt0
  go d ctx Bt1           = Bt1
  go d ctx (BitM f t)    = BitM (go d ctx f) (go d ctx t)
  go d ctx Nat           = Nat
  go d ctx Zer           = Zer
  go d ctx (Suc n)       = Suc (go d ctx n)
  go d ctx (NatM z s)    = NatM (go d ctx z) (go d ctx s)
  go d ctx (Lst t)       = Lst (go d ctx t)
  go d ctx Nil           = Nil
  go d ctx (Con h t)     = Con (go d ctx h) (go d ctx t)
  go d ctx (LstM n c)    = LstM (go d ctx n) (go d ctx c)
  go d ctx (ADT n ts)    = ADT n (map (go d ctx) ts)
  go d ctx (Ctr n ts)    = Ctr n (map (go d ctx) ts)
  go d ctx (ADTM n cs m) = ADTM n [(c, go d ctx t) | (c, t) <- cs] (fmap (go d ctx) m)
  go d ctx (Sig a b)     = Sig (go d ctx a) (go d ctx b)
  go d ctx (Tup a b)     = Tup (go d ctx a) (go d ctx b)
  go d ctx (SigM f)      = SigM (go d ctx f)
  go d ctx (All a b)     = All (go d ctx a) (go d ctx b)
  go d ctx (Lam n t f)   = Lam n (fmap (go d ctx) t) (\x -> go (d+1) ((n,d):ctx) (f x))
  go d ctx (App f x)     = App (go d ctx f) (go d ctx x)
  go d ctx (Eql t a b)   = Eql (go d ctx t) (go d ctx a) (go d ctx b)
  go d ctx Rfl           = Rfl
  go d ctx (EqlM f)      = EqlM (go d ctx f)
  go d ctx (Met i t x)   = Met i (go d ctx t) (map (go d ctx) x)
  go d ctx Era           = Era
  go d ctx (Sup l a b)   = Sup (go d ctx l) (go d ctx a) (go d ctx b)
  go d ctx (SupM l f)    = SupM (go d ctx l) (go d ctx f)
  go d ctx (Frk l a b)   = frk d ctx l a b
  go d ctx (Rwt e f)     = Rwt (go d ctx e) (go d ctx f)
  go d ctx (Num t)       = Num t
  go d ctx (Val v)       = Val v
  go d ctx (Op2 o a b)   = Op2 o (go d ctx a) (go d ctx b)
  go d ctx (Op1 o a)     = Op1 o (go d ctx a)
  go d ctx (Pri p)       = Pri p
  go d ctx (Log s x)     = Log (go d ctx s) (go d ctx x)
  go d ctx (Loc s t)     = Loc s (go d ctx t)
  go d ctx (Pat s m c)   = Pat (map (go d ctx) s) [(k, go d ctx v) | (k,v) <- m] [(p, go d (ctxCs p) f) | (p, f) <- c]
    where ctxCs  p = ctx ++ map (\(k,v) -> (k, d)) m ++ ctxPat p
          ctxPat p = map (\k -> (k, d)) (S.toList (S.map fst (S.unions (map (freeVars book S.empty) p))))

  frk :: Int -> [(Name, Int)] -> Term -> Term -> Term -> Term
  frk d ctx l a b = buildSupMs vars where
    vars =  shadowCtx (filter (\x -> fst x `S.member` free) (reverse ctx))
    free = case cut l of
      -- 'l' must be a non-superposed U64 so we can remove it from the forked vars as a (reasonable) optimization.
      Var n _ -> S.delete n (S.map fst (freeVars book S.empty a `S.union` freeVars book S.empty b))
      _       -> S.map fst (freeVars book S.empty a `S.union` freeVars book S.empty b)
    -- Build nested SupM matches for each context variable
    buildSupMs :: [(Name, Int)] -> Term
    buildSupMs [] = Sup l a' b' where
      ls = [(n, Var (n++"0") 0) | (n, _) <- vars]
      rs = [(n, Var (n++"1") 0) | (n, _) <- vars]
      a' = bindVarByNameMany ls (go d ctx a)
      b' = bindVarByNameMany rs (go d ctx b)
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
