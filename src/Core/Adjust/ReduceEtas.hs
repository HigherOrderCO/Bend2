{-./../Type.hs-}

-- Eta-Form
-- ========
--
-- This module performs a generalized eta-reduction, 
-- transforming nested lambda-match patterns into more efficient forms.
--
-- The final form has pulled up to the surface-most level of the term tree 
-- all lambda matches applied on variables (i.e. subterms like λ{..}(x))
--
-- Important: this does not changes `SupM` eliminators.
--
-- Basic Transformation:
-- --------------------
--
-- λx. λy. (1n, λ{A: 2n ;B: 3n}(x))
-- ---------------------------------- reduceEtas
-- λ{A: λy.(1n, 2n); B: λy.(1n, 3n)}
--
--
-- In General:
-- ----------
--
-- λx. t[
--        λ{A(a1,..):tA_1[x, a1..]; ..; B(b1,..): tB_1[x, b1..]; ..}(x),
--        λ{A(a1,..):tA_2[x, a1..]; ..; B(b1,..): tB_2[x, b1..]; ..}(x),
--   ...] 
--  ------------------------------------------------------------------- reduceEtas
--  λ{
--    A: t[
--          tA_1[A(a1,..), a1..]],
--          tA_2[A(a1,..), a1..]],
--     ...];
--    B: t[
--          tB_1[B(b1,..), b1..]],
--          tB_2[B(b1,..), b2..]],
--     ...];
--    ...
--  }
--
--  That is, finding a pattern λx. term[λ{..}(x)] triggers the rewriting of the term into a λ{..} form,
--  where each clause of the new λ{..} is the original `term` after substituting its subterms of form λ{..}(x)
--  by the value that those subterms should have given that `x` has the value dictated by the clause within which it is now located
--
-- Examples:
-- ---------
-- 1. Simple eta-reduction:
--    λn. λ{0n:Z; 1n+:S}(n) ~> λ{0n:Z; 1n+:S}
--
-- 2. With intermediate lambdas:
--    λa. λb. λ{0n:Z; 1n+:S}(a) ~> λ{0n:λb.Z; 1n+:λp.λb.S}
--
-- 3. With scrutinee reconstruction:
--    λa. λ{0n:a; 1n+:λp. 1n+p}(a) ~> λ{0n: 0n; 1n+:λp. 1n+p}
--
-- Implementation:
-- ---------------
-- reduceEtas -> at each subterm λx.f, uses isEtaLong to check 
--               whether f contains λ{..}(x). If it does,
--               then it uses resolveMatches to produce its output
-- isEtaLong nam -> at each subterm f(x), if x is the variable 'nam'
--               from the lambda given from reduceEtas, and f is a λ{..}, 
--               then return a label encoding which kind of λ{..}. Store information about
--               clause argument types, and return STOP if incompatible information is found
-- resolveMatches -> given elim label, at each term f(x), if `f` is λ{..} 
--               of a kind matching the elim label, then replace this application by
--               the the clause of f that corresponds to the one determined by reduceEtas

{-# LANGUAGE ViewPatterns #-}
module Core.Adjust.ReduceEtas where

import Core.Type
import Core.Equal
import Core.Bind
import Core.Show
import qualified Data.Set as S
import qualified Data.Map as M
import Data.List (union)
import Debug.Trace
import Data.Maybe (isJust, fromJust, fromMaybe)
import Control.Applicative

expandElimApps :: Int -> Span -> Book -> Term -> Term
expandElimApps d span book term = case term of
  App f x -> case (cut f, cut x) of
    (UniM f, One) -> 
      expandElimApps d span book f
    (BitM f t, Bt0) -> 
      expandElimApps d span book f
    (BitM f t, Bt1) -> 
      expandElimApps d span book t
    (NatM z s, Zer) -> 
      expandElimApps d span book z
    (NatM z s, Suc n) -> 
      expandElimApps d span book (App s n)
    (LstM n c, Nil) -> 
      expandElimApps d span book n
    (LstM n c, Con h t) -> 
      expandElimApps d span book (App (App c h) t)
    (SigM g, Tup a b) -> 
      expandElimApps d span book (App (App g a) b)
    _ -> App (expandElimApps d span book f) (expandElimApps d span book x)
  
  -- Recursive cases for all other constructors
  Loc l t       -> Loc l (expandElimApps d l book t)
  Lam k mty f   -> Lam k (fmap (expandElimApps d span book) mty) (\x -> expandElimApps (d+1) span book (f x))
  Fix n f       -> Fix n (\v -> expandElimApps (d+1) span book (f v))
  Let n mty v f -> Let n (fmap (expandElimApps d span book) mty) 
                         (expandElimApps d span book v) 
                         (\v' -> expandElimApps (d+1) span book (f v'))
  Use n v f     -> Use n (expandElimApps d span book v) (\v' -> expandElimApps (d+1) span book (f v'))
  Chk t ty      -> Chk (expandElimApps d span book t) (expandElimApps d span book ty)
  UniM f        -> UniM (expandElimApps d span book f)
  BitM f g      -> BitM (expandElimApps d span book f) (expandElimApps d span book g)
  Suc t         -> Suc (expandElimApps d span book t)
  NatM z s      -> NatM (expandElimApps d span book z) (expandElimApps d span book s)
  IO t          -> IO (expandElimApps d span book t)
  Lst ty        -> Lst (expandElimApps d span book ty)
  Con h t       -> Con (expandElimApps d span book h) (expandElimApps d span book t)
  LstM nil c    -> LstM (expandElimApps d span book nil) (expandElimApps d span book c)
  EnuM cs def   -> EnuM [(s, expandElimApps d span book v) | (s,v) <- cs] (expandElimApps d span book def)
  Op2 o a b     -> Op2 o (expandElimApps d span book a) (expandElimApps d span book b)
  Op1 o a       -> Op1 o (expandElimApps d span book a)
  Sig a b       -> Sig (expandElimApps d span book a) (expandElimApps d span book b)
  Tup a b       -> Tup (expandElimApps d span book a) (expandElimApps d span book b)
  SigM f        -> SigM (expandElimApps d span book f)
  All a b       -> All (expandElimApps d span book a) (expandElimApps d span book b)
  Eql ty a b    -> Eql (expandElimApps d span book ty) (expandElimApps d span book a) (expandElimApps d span book b)
  EqlM f        -> EqlM (expandElimApps d span book f)
  Rwt e f       -> Rwt (expandElimApps d span book e) (expandElimApps d span book f)
  Met n ty args -> Met n (expandElimApps d span book ty) (map (expandElimApps d span book) args)
  Sup l a b     -> Sup (expandElimApps d span book l) (expandElimApps d span book a) (expandElimApps d span book b)
  SupM l f      -> SupM (expandElimApps d span book l) (expandElimApps d span book f)
  Log s x       -> Log (expandElimApps d span book s) (expandElimApps d span book x)
  Pat ss ms cs  -> Pat (map (expandElimApps d span book) ss) 
                       [(k, expandElimApps d span book v) | (k,v) <- ms] 
                       [(map (expandElimApps d span book) ps, expandElimApps d span book rhs) | (ps,rhs) <- cs]
  Frk l a b     -> Frk (expandElimApps d span book l) (expandElimApps d span book a) (expandElimApps d span book b)
  Tst x         -> Tst (expandElimApps d span book x)
  Sub t         -> Sub (expandElimApps d span book t)
  
  -- Base cases (no recursion needed)
  Var n i       -> Var n i
  Ref n i       -> Ref n i
  Set           -> Set
  Emp           -> Emp
  EmpM          -> EmpM
  Uni           -> Uni
  One           -> One
  Bit           -> Bit
  Bt0           -> Bt0
  Bt1           -> Bt1
  Nat           -> Nat
  Zer           -> Zer
  Nil           -> Nil
  Enu ss        -> Enu ss
  Sym s         -> Sym s
  Num nt        -> Num nt
  Val nv        -> Val nv
  Rfl           -> Rfl
  Era           -> Era
  Pri p         -> Pri p

-- Main eta-reduction function
-- 1) Assumes the `term` at call time is completely in HOAS bind form.
--    Otherwise, (f Var nam d) is not useful, and variable capture/shadowing can happen.
-- 2) Uses bindVarByName for the reconstructions x ~> A(a1,a2,..) and rebindings (after (f (Var nam d)) destroyed them)
--    bindVarByIndex/Name is blind to `d`, hence the use of unique `nam`
-- 3) Receives the eliminator type and var names a1.. from isEtaLong
-- 4) The span in the ElimLabel is the span of the inner eliminator found by isEtaLong.
--    This span bubbles up to become the span of the new outer eliminator we synthesize,
--    since the new eliminator has no natural span of its own (it didn't exist in the source).
-- 5) Rewrites the subterms using resolveMatches
--
-- Returns  : term in the form λ{A(a1..):λ{B:..}; ..}
-- Important: this does not changes `SupM` eliminators.
reduceEtas :: Int -> Span -> Book -> Term -> Term
reduceEtas d span book (Loc l term) = Loc l (reduceEtas d l book term)
reduceEtas d span book term = 
  case term of
  Lam k mty f ->
      -- The "$" prefix ensures `nam` won't clash with user variables
      let nam = "$"++show d in
      let eta = isEtaLong d span book nam (f (Var nam d)) in
      case eta of
        EMPM spa -> Loc spa $ EmpM
        EQLM spa -> Loc spa $ EqlM refl 
            where
            refl = reduceEtas d span book $ bindVarByName nam Rfl (resolveMatches span nam eta 0 "" [] (f (Var nam d)))
        UNIM spa -> Loc spa $ UniM u
            where
            u    = reduceEtas d span book $ bindVarByName nam One (resolveMatches span nam eta 0 "" [] (f (Var nam d)))
        BITM spa -> Loc spa $ BitM fl tr 
            where
            fl   = reduceEtas d span book $ bindVarByName nam Bt0 (resolveMatches span nam eta 0 "" [] (f (Var nam d)))
            tr   = reduceEtas d span book $ bindVarByName nam Bt1 (resolveMatches span nam eta 1 "" [] (f (Var nam d)))
        NATM spa nams@[p] anns@[pAnn] -> Loc spa $ NatM z s 
            where
            z    = reduceEtas d span book $ bindVarByName nam Zer (resolveMatches span nam eta 0 "" [] (f (Var nam d)))
            s    = reduceEtas d span book $ (Lam p pAnn (\q -> 
                                             bindVarByName nam (Suc q) (resolveMatches span nam eta 1 "" [Sub q] (f (Var nam d)))))
        LSTM spa nams@[h,t] anns@[hAnn, tAnn] -> Loc spa $ LstM nil cons 
            where
            nil  = reduceEtas d span book $ bindVarByName nam Nil (resolveMatches span nam eta 0 "" [] (f (Var nam d)))
            cons = reduceEtas d span book $ (Lam h hAnn (\h ->
                                             Lam t tAnn (\t ->
                                             bindVarByName nam (Con h t) (resolveMatches span nam eta 1 "" [Sub h, Sub t] (f (Var nam d))))))
        SIGM spa nams@[a,b] anns@[aAnn, bAnn] -> Loc spa $ SigM pair
            where
            pair = reduceEtas d span book $ (Lam a aAnn (\a ->
                                             Lam b bAnn (\b ->
                                             bindVarByName nam (Tup a b) (resolveMatches span nam eta 0 "" [Sub a, Sub b] (f (Var nam d))))))
        ENUM spa syms compl nams@[de] anns@[deAnn] -> Loc spa $ EnuM cases def 
          where
          cases = map (\sym -> (sym, reduceEtas d span book $ bindVarByName nam (Sym sym) (resolveMatches span nam eta 0 sym [] (f (Var nam d))))) syms
          def = if compl
                then 
                  -- trace ("HUM1: " ++ show (bindVarByName nam (Var nam 0) (resolveMatches span nam eta (-1) "" [Var nam 0] (f (Var nam d))))) $ 
                  -- trace ("HUM2: " ++ show (Lam de deAnn (\q -> bindVarByName nam q (resolveMatches span nam eta (-1) "" [Sub q] (f (Var nam d)))))) $ 
                  -- trace ("HUM3: " ++ show (reduceEtas d span book $ Lam de deAnn (\q -> bindVarByName nam q (resolveMatches span nam eta (-1) "" [Sub q] (f (Var nam d)))))) $ 
                  reduceEtas d span book (Lam de deAnn (\q -> reduceEtas d span book $ bindVarByName nam q (resolveMatches span nam eta (-1) "" [Sub q] (f (Var nam d)))))
                  -- reduceEtas d span book (Lam de deAnn (\q -> bindVarByName nam q (resolveMatches span nam eta (-1) "" [Sub q] (f (Var nam d)))))
                else One
        _ -> Lam k mty (\x -> reduceEtas (d+1) span book (f x))
        -- SUPM lab -> not reduced
  Var n i       -> Var n i
  Ref n i       -> Ref n i
  Sub t'        -> Sub t'
  Fix n f       -> Fix n (\v -> reduceEtas (d+1) span book (f v))
  Let n mty v f -> Let n (fmap (reduceEtas d span book) mty) (reduceEtas d span book v) (\v' -> reduceEtas (d+1) span book (f v'))
  Use n v f     -> Use n (reduceEtas d span book v) (\v' -> reduceEtas (d+1) span book (f v'))
  Set           -> Set
  Chk t' ty     -> Chk (reduceEtas d span book t') (reduceEtas d span book ty)
  Emp           -> Emp
  EmpM          -> EmpM
  Uni           -> Uni
  One           -> One
  UniM f        -> UniM (reduceEtas d span book f)
  Bit           -> Bit
  Bt0           -> Bt0
  Bt1           -> Bt1
  BitM f g      -> BitM (reduceEtas d span book f) (reduceEtas d span book g)
  Nat           -> Nat
  Zer           -> Zer
  Suc t'        -> Suc (reduceEtas d span book t')
  NatM z s      -> NatM (reduceEtas d span book z) (reduceEtas d span book s)
  IO t          -> IO (reduceEtas d span book t)
  Lst ty        -> Lst (reduceEtas d span book ty)
  Nil           -> Nil
  Con h t'      -> Con (reduceEtas d span book h) (reduceEtas d span book t')
  LstM nil c    -> LstM (reduceEtas d span book nil) (reduceEtas d span book c)
  Enu ss        -> Enu ss
  Sym s         -> Sym s
  EnuM cs def   -> EnuM [(s, reduceEtas d span book v) | (s,v) <- cs] (reduceEtas d span book def)
  Num nt        -> Num nt
  Val nv        -> Val nv
  Op2 o a b     -> Op2 o (reduceEtas d span book a) (reduceEtas d span book b)
  Op1 o a       -> Op1 o (reduceEtas d span book a)
  Sig a b       -> Sig (reduceEtas d span book a) (reduceEtas d span book b)
  Tup a b       -> Tup (reduceEtas d span book a) (reduceEtas d span book b)
  SigM f        -> SigM (reduceEtas d span book f)
  All a b       -> All (reduceEtas d span book a) (reduceEtas d span book b)
  App f x -> case cut f of
    Lam k Nothing b -> reduceEtas d span book (b x)
    _ -> let f' = reduceEtas d span book f in
         case cut f' of
           Lam k Nothing b -> reduceEtas d span book (b x)
           _ -> App f' (reduceEtas d span book x)
  Eql ty a b    -> Eql (reduceEtas d span book ty) (reduceEtas d span book a) (reduceEtas d span book b)
  Rfl           -> Rfl
  EqlM f        -> EqlM (reduceEtas d span book f)
  Rwt e f       -> Rwt (reduceEtas d span book e) (reduceEtas d span book f)
  Met n ty args -> Met n (reduceEtas d span book ty) (map (reduceEtas d span book) args)
  Era           -> Era
  Sup l a b     -> Sup (reduceEtas d span book l) (reduceEtas d span book a) (reduceEtas d span book b)
  SupM l f      -> SupM (reduceEtas d span book l) (reduceEtas d span book f)
--Loc s t'      -> Loc s (reduceEtas d span t')
  Log s x       -> Log (reduceEtas d span book s) (reduceEtas d span book x)
  Pri p         -> Pri p
  Pat ss ms cs  -> Pat (map (reduceEtas d span book) ss) [(k, reduceEtas d span book v) | (k,v) <- ms] [(map (reduceEtas d span book) ps, reduceEtas d span book rhs) | (ps,rhs) <- cs]
  Frk l a b     -> Frk (reduceEtas d span book l) (reduceEtas d span book a) (reduceEtas d span book b)
  Tst x         -> Tst (reduceEtas d span book x)

-- Substitution of eliminator applications with their clauses
-- 1) Finds App nodes where f is an eliminator and x is 'nam'
-- 2) Replaces the application with the branch selected by 'clause':
--    2.1) clause 0 = first branch (e.g., zero for Nat, nil for List)
--    2.2) clause 1 = second branch (e.g., successor for Nat, cons for List)
--    2.3) For enums, 'sym' determines which symbol's branch to use
-- 3) For branches with parameters, uses 'args' to apply them via appInnerArg
-- 4) Recursively processes the selected branch to handle nested eliminators
--
-- Returns: NatM z s applied to 'nam' with clause=0           -> returns z
--          NatM z s applied to 'nam' with clause=1, args=[p] -> returns s(p)[nam -> 1n+p]
resolveMatches :: Span -> Name -> ElimLabel -> Int -> String -> [Term] -> Term -> Term
resolveMatches span nam elim clause sym args (Loc span' term) = Loc span' (resolveMatches span' nam elim clause sym args term)
resolveMatches span nam elim clause sym args t = case t of
  App f x      ->
    case cut x of
      (Var k i) -> if k == nam
        then case (cut f, elim, args) of
          (UniM u       , UNIM _        , [])    -> resolveMatches span nam elim clause sym args $ u
          (BitM fl tr   , BITM _        , [])    -> resolveMatches span nam elim clause sym args $ ([fl, tr] !! clause)
          (NatM z s     , NATM _ _ _    , [])    -> resolveMatches span nam elim clause sym args $ z
          (NatM z s     , NATM _ _ _    , [p])   -> resolveMatches span nam elim clause sym args $ appArgs s args 0
       -- (EmpM         , EMPM _        , [])    -> resolveMatches span nam elim clause sym args $ 
          (LstM nil cons, LSTM _ _ _    , [])    -> resolveMatches span nam elim clause sym args $ nil
          (LstM nil cons, LSTM _ _ _    , [h,t]) -> resolveMatches span nam elim clause sym args $ appArgs cons args 0
          (SigM pair    , SIGM _ _ _    , [a,b]) -> resolveMatches span nam elim clause sym args $ appArgs pair args 0
          (EqlM refl    , EQLM _        , [])    -> resolveMatches span nam elim clause sym args refl
          (EnuM cs def  , ENUM _ _ _ _ _, [q])   -> resolveMatches span nam elim clause sym args $ appArgs def args 0
          (EnuM cs def  , ENUM _ _ _ _ _, [])    -> case lookup sym cs of
                                Just branch  -> resolveMatches span nam elim clause sym args $ branch
                                Nothing      -> resolveMatches span nam elim clause sym args $ appArgs def [(Var k i)] 0
          _ -> App (resolveMatches span nam elim clause sym args f) (resolveMatches span nam elim clause sym args x)
        else   App (resolveMatches span nam elim clause sym args f) (resolveMatches span nam elim clause sym args x)
      _     -> App (resolveMatches span nam elim clause sym args f) (resolveMatches span nam elim clause sym args x)
    where
      appArgs :: Term -> [Term] -> Int -> Term
      appArgs f [] _ = f
      appArgs (Use k v b) args skip    = Use k v (\v -> (appArgs (b v) args skip))
      appArgs (Let k mt v b) args skip = Let k mt v (\v -> (appArgs (b v) args skip))
      appArgs (Chk x t) args skip      = Chk (appArgs t args skip) t
      appArgs (Loc l t) args skip      = Loc l (appArgs t args skip)
      appArgs (Log s t) args skip      = Log s (appArgs t args skip)
      appArgs (App f x) args skip      = App (appArgs f args (skip+1)) x -- skip arguments consumed by x
      appArgs f args@(arg:rest) skip@0 = case cut f of 
        Lam k mt b  -> appArgs (b arg) rest skip
        EqlM f      -> App (EqlM (appArgs f rest skip)) arg
        UniM f      -> App (UniM (appArgs f rest skip)) arg
        BitM f t    -> App (BitM (appArgs f rest skip) (appArgs f rest     skip)) arg
        NatM z s    -> App (NatM (appArgs z rest skip) (appArgs s rest (skip+1))) arg
        LstM n c    -> App (LstM (appArgs n rest skip) (appArgs c rest (skip+2))) arg
        SigM g      -> App (SigM (appArgs g rest (skip+2))) arg
        EnuM cs def -> App (EnuM (map (\(s,t) -> (s, appArgs t rest skip)) cs) (appArgs def rest (skip+1))) arg
        _           -> foldl App f args 
      appArgs f args@(arg:rest) skip = case cut f of 
        Lam k mt b  -> Lam k mt (\x -> (appArgs (b x) args (skip-1)))
        EqlM f      -> EqlM (appArgs f args (skip-1))
        UniM f      -> UniM (appArgs f args (skip-1))
        BitM f t    -> BitM (appArgs f args (skip-1)) (appArgs f args (skip-1))
        NatM z s    -> NatM (appArgs z args (skip-1)) (appArgs s args (skip-1+1))
        LstM n c    -> LstM (appArgs n args (skip-1)) (appArgs c args (skip-1+2))
        SigM g      -> SigM (appArgs g args (skip-1+2))
        EnuM cs def -> EnuM (map (\(s,t) -> (s, appArgs t args (skip-1))) cs) (appArgs def args (skip-1+1))
        _           -> foldl App f args
  -- Not an eliminator application, just propagate deeper
  Lam k ty f   -> Lam k (fmap (resolveMatches span nam elim clause sym args) ty) (\x -> resolveMatches span nam elim clause sym args (f x))
  Var k i      -> Var k i
  Ref k i      -> Ref k i
  Sub t'       -> Sub (resolveMatches span nam elim clause sym args t')
  Fix k f      -> Fix k (\x -> resolveMatches span nam elim clause sym args (f x))
  Let k ty v f -> Let k (fmap (resolveMatches span nam elim clause sym args) ty) (resolveMatches span nam elim clause sym args v) (\x -> resolveMatches span nam elim clause sym args (f x))
  Use k v f    -> Use k (resolveMatches span nam elim clause sym args v) (\x -> resolveMatches span nam elim clause sym args (f x))
  Set          -> Set
  Chk t' ty    -> Chk (resolveMatches span nam elim clause sym args t') (resolveMatches span nam elim clause sym args ty)
  Emp          -> Emp
  EmpM         -> EmpM
  Uni          -> Uni
  One          -> One
  UniM f       -> UniM (resolveMatches span nam elim clause sym args f)
  Bit          -> Bit
  Bt0          -> Bt0
  Bt1          -> Bt1
  BitM f g     -> BitM (resolveMatches span nam elim clause sym args f) (resolveMatches span nam elim clause sym args g)
  Nat          -> Nat
  Zer          -> Zer
  Suc t'       -> Suc (resolveMatches span nam elim clause sym args t')
  NatM z s     -> NatM (resolveMatches span nam elim clause sym args z) (resolveMatches span nam elim clause sym args s)
  IO t         -> IO (resolveMatches span nam elim clause sym args t)
  Lst ty       -> Lst (resolveMatches span nam elim clause sym args ty)
  Nil          -> Nil
  Con h t'     -> Con (resolveMatches span nam elim clause sym args h) (resolveMatches span nam elim clause sym args t')
  LstM nil c   -> LstM (resolveMatches span nam elim clause sym args nil) (resolveMatches span nam elim clause sym args c)
  Enu syms     -> Enu syms
  Sym s        -> Sym s
  EnuM cs def  -> EnuM (map (\(s,t') -> (s, resolveMatches span nam elim clause sym args t')) cs) (resolveMatches span nam elim clause sym args def)
  Num typ      -> Num typ
  Val v        -> Val v
  Op2 op a b   -> Op2 op (resolveMatches span nam elim clause sym args a) (resolveMatches span nam elim clause sym args b)
  Op1 op a     -> Op1 op (resolveMatches span nam elim clause sym args a)
  Sig a b      -> Sig (resolveMatches span nam elim clause sym args a) (resolveMatches span nam elim clause sym args b)
  Tup a b      -> Tup (resolveMatches span nam elim clause sym args a) (resolveMatches span nam elim clause sym args b)
  SigM f       -> SigM (resolveMatches span nam elim clause sym args f)
  All a b      -> All (resolveMatches span nam elim clause sym args a) (resolveMatches span nam elim clause sym args b)
  Eql ty a b   -> Eql (resolveMatches span nam elim clause sym args ty) (resolveMatches span nam elim clause sym args a) (resolveMatches span nam elim clause sym args b)
  Rfl          -> Rfl
  EqlM f       -> EqlM (resolveMatches span nam elim clause sym args f)
  Rwt e f      -> Rwt (resolveMatches span nam elim clause sym args e) (resolveMatches span nam elim clause sym args f)
  Met name ty as -> Met name (resolveMatches span nam elim clause sym args ty) (map (resolveMatches span nam elim clause sym args) as)
  Era          -> Era
  Sup l' a b   -> Sup (resolveMatches span nam elim clause sym args l') (resolveMatches span nam elim clause sym args a) (resolveMatches span nam elim clause sym args b)
  SupM l' f    -> SupM (resolveMatches span nam elim clause sym args l') (resolveMatches span nam elim clause sym args f)
--Loc l t'     -> Loc span (resolveMatches span nam elim clause sym args t')
  Log s x      -> Log (resolveMatches span nam elim clause sym args s) (resolveMatches span nam elim clause sym args x)
  Pri pf       -> Pri pf
  Pat ss ms cs -> Pat (map (resolveMatches span nam elim clause sym args) ss)
                      (map (\(m,t') -> (m, resolveMatches span nam elim clause sym args t')) ms)
                      (map (\(ps,rhs) -> (map (resolveMatches span nam elim clause sym args) ps, resolveMatches span nam elim clause sym args rhs)) cs)
  Frk l' a b   -> Frk (resolveMatches span nam elim clause sym args l') 
                      (resolveMatches span nam elim clause sym args a) 
                      (resolveMatches span nam elim clause sym args b)
  Tst x        -> Tst (resolveMatches span nam elim clause sym args x)

-- Detection of the pattern λnam. ... λ{..}(nam)
-- 1) At App nodes: checks if argument is 'nam' and function is an eliminator
-- 2) Collects parameter names from eliminators for later reconstruction
--    2.1) NONE means no eliminator on 'nam' was found
--    2.2) Multiple compatible eliminators combine (e.g., NATM <+> NATM = NATM)
--    2.3) Incompatible eliminators cancel (e.g., NATM <+> BITM = NONE)
-- 3) Uses getVarNames to get the names of the clause arguments, if they are given
-- 4) Captures the span of each eliminator found, which will become the span of
--    the synthesized outer eliminator in reduceEtas (since that new eliminator
--    has no span of its own)
--
-- Returns: from λx. (λ{0:Z; S:...}(x), λ{0:W; S:...}(x)) 
-- the label NATM [pred_name_from_S]
isEtaLong :: Int -> Span -> Book -> Name -> Term -> ElimLabel
isEtaLong d span book nam (Loc spa t) = isEtaLong d spa book nam t
isEtaLong d span book nam t = case t of
  Lam k mt f  -> case mt of
    Just t  -> if k == nam then isEtaLong d span book nam t else combLabels d book (isEtaLong d span book nam t) (isEtaLong (d+1) span book nam (f (Var k d)))
    Nothing -> if k == nam then NONE else isEtaLong (d+1) span book nam (f (Var k d))
  App f x     ->
    case cut x of
      (Var k _) -> if k == nam
        then
          case (cut f, getAnnotations d book f) of
       -- SupM l _    -> not eliminated
          (EqlM _  , _)            -> combLabels d book (EQLM span) (isEtaLong d span book nam f)
          (EmpM    , _)            -> combLabels d book (EMPM span) (isEtaLong d span book nam f)
          (UniM _  , _)            -> combLabels d book (UNIM span) (isEtaLong d span book nam f)
          (BitM _ _, _)            -> combLabels d book (BITM span) (isEtaLong d span book nam f)
          (NatM _ s   , Just anns) -> combLabels d book (NATM span (getVarNames s ["p"]    ) anns) (isEtaLong d span book nam f)
          (LstM _ c   , Just anns) -> combLabels d book (LSTM span (getVarNames c ["h","t"]) anns) (isEtaLong d span book nam f)
          (SigM g     , Just anns) -> combLabels d book (SIGM span (getVarNames g ["a","b"]) anns) (isEtaLong d span book nam f)
          (EnuM cs def, Just anns) -> combLabels d book (ENUM span (map fst cs) (isLam def) (getVarNames def ["t"]) anns) (isEtaLong d span book nam f)
          (NatM _ s   , Nothing)   -> STOP
          (LstM _ c   , Nothing)   -> STOP
          (SigM g     , Nothing)   -> STOP
          (EnuM cs def, Nothing)   -> STOP
          (_,_)           -> isEtaLong d span book nam f
        else
            combLabels d book (isEtaLong d span book nam f) (isEtaLong d span book nam x)
      _ -> combLabels d book (isEtaLong d span book nam f) (isEtaLong d span book nam x)
  Var _ _     -> NONE
  Ref _ _     -> NONE
  Sub t'      -> isEtaLong d span book nam t'
  Fix k f     -> isEtaLong (d+1) span book nam (f (Var k d))
  Let k t v f -> let def = combLabels d book (isEtaLong d span book nam v) (isEtaLong (d+1) span book nam (f (Var k d))) 
                 in fromMaybe def (fmap (\typ -> combLabels d book def (isEtaLong d span book nam typ)) t)
  Use k v f   -> combLabels d book (isEtaLong d span book nam v) (isEtaLong (d+1) span book nam (f (Var k d)))
  Set         -> NONE
  Chk t' ty   -> combLabels d book (isEtaLong d span book nam t') (isEtaLong d span book nam ty)
  Emp         -> NONE
  EmpM        -> NONE
  Uni         -> NONE
  One         -> NONE
  UniM f      -> isEtaLong d span book nam f
  Bit         -> NONE
  Bt0         -> NONE
  Bt1         -> NONE
  BitM f g    -> combLabels d book (isEtaLong d span book nam f) (isEtaLong d span book nam g)
  Nat         -> NONE
  Zer         -> NONE
  Suc t'      -> isEtaLong d span book nam t'
  NatM z s    -> combLabels d book (isEtaLong d span book nam z) (isEtaLong d span book nam s)
  IO t        -> isEtaLong d span book nam t
  Lst ty      -> isEtaLong d span book nam ty
  Nil         -> NONE
  Con h t'    -> combLabels d book (isEtaLong d span book nam h) (isEtaLong d span book nam t')
  LstM nil c  -> combLabels d book (isEtaLong d span book nam nil) (isEtaLong d span book nam c)
  Enu _       -> NONE
  Sym _       -> NONE
  EnuM cs def -> foldr (combLabels d book) (isEtaLong d span book nam def) (map (isEtaLong d span book nam . snd) cs)
  Num _       -> NONE
  Val _       -> NONE
  Op2 _ a b   -> combLabels d book (isEtaLong d span book nam a) (isEtaLong d span book nam b)
  Op1 _ a     -> isEtaLong d span book nam a
  Sig a b     -> combLabels d book (isEtaLong d span book nam a) (isEtaLong d span book nam b)
  Tup a b     -> combLabels d book (isEtaLong d span book nam a) (isEtaLong d span book nam b)
  SigM f      -> isEtaLong d span book nam f
  All a b     -> combLabels d book (isEtaLong d span book nam a) (isEtaLong d span book nam b)
  Eql ty a b  -> foldr (combLabels d book) NONE [isEtaLong d span book nam ty, isEtaLong d span book nam a, isEtaLong d span book nam b]
  Rfl         -> NONE
  EqlM f      -> isEtaLong d span book nam f
  Rwt e f     -> combLabels d book (isEtaLong d span book nam e) (isEtaLong d span book nam f)
  Met _ ty cx -> combLabels d book (isEtaLong d span book nam ty) (foldr (combLabels d book) NONE (map (isEtaLong d span book nam) cx))
  Era         -> NONE
  Sup l a b   -> foldr (combLabels d book) NONE [isEtaLong d span book nam l, isEtaLong d span book nam a, isEtaLong d span book nam b]
  SupM l f    -> combLabels d book (isEtaLong d span book nam l) (isEtaLong d span book nam f)
  -- Loc _ t'    -> isEtaLong d span book nam t'
  Log s x     -> combLabels d book (isEtaLong d span book nam s) (isEtaLong d span book nam x)
  Pri _       -> NONE
  Pat ss ms cs -> foldr (combLabels d book) NONE (map (isEtaLong d span book nam) ss ++ map (isEtaLong d span book nam . snd) ms ++ concatMap (\(ps, rhs) -> map (isEtaLong d span book nam) ps ++ [isEtaLong d span book nam rhs]) cs)
  Frk l a b   -> foldr (combLabels d book) NONE [isEtaLong d span book nam l, isEtaLong d span book nam a, isEtaLong d span book nam b]
  Tst x       -> isEtaLong d span book nam x

-- Auxiliary definitions / Utils
-- ------------------------------

-- SUPM not reduced
data ElimLabel
  = UNIM Span                                     -- Span of the original eliminator
  | BITM Span                                     -- Span of the original eliminator
  | NATM Span [String] [Maybe Term]               -- Span of the original eliminator, [predName], [clause arg annotations]
  | EMPM Span                                     -- Span of the original eliminator
  | LSTM Span [String] [Maybe Term]               -- Span of the original eliminator, [headName,tailName], [clause arg annotations]
  | SIGM Span [String] [Maybe Term]               -- Span of the original eliminator, [fstName , sndName], [clause arg annotations]
  | EQLM Span                                     -- Span of the original eliminator
  | ENUM Span [String] Bool [String] [Maybe Term] -- Span of the original eliminator, [symbolNames], isNotComplete, [defaultArgName], [clause arg annotations]
  | NONE
  | STOP
  deriving Show -- SUPM not reduced

-- Combines eliminator labels from multiple λ{..}(nam) occurrences
-- 1) STOP propagates: any combination with STOP yields STOP
-- 2) NONE acts as identity: anything combined with NONE stays unchanged
-- 3) Same eliminator types combine by keeping first's parameters
--    - Simple types (UNIM/BITM/EMPM/EQLM): just keep first
--    - Annotated types (NATM/LSTM/SIGM/ENUM): merge annotations via combAnns, STOP if incompatible
--    - ENUM special case: also unions symbol sets and conjoins completeness flags
-- 4) Different eliminator types yield STOP (mixed patterns can't be eta-reduced)
--
-- Returns: NATM [p,q] <+> NATM [r,q] -> NATM [p,q]
--          NATM [p,q] <+> BITM       -> STOP
combLabels :: Int -> Book -> ElimLabel -> ElimLabel -> ElimLabel
combLabels d book lab1 lab2 = case (lab1, lab2) of
  (STOP, x)                      -> STOP
  (x, STOP)                      -> STOP
  (NONE, x)                      -> x
  (x, NONE)                      -> x
  (UNIM l1, UNIM l2)             -> UNIM l1
  (BITM l1, BITM l2)             -> BITM l1
  (EMPM l1, EMPM l2)             -> EMPM l1
  (EQLM l1, EQLM l2)             -> EQLM l1
  (NATM l1 s1 a1, NATM l2 s2 a2) -> case (combAnns a1 a2) of
    Just a -> NATM l1 s1 a
    _      -> STOP
  (LSTM l1 s1 a1, LSTM l2 s2 a2) -> case (combAnns a1 a2) of 
    Just a -> LSTM l1 s1 a
    _      -> STOP
  (SIGM l1 s1 a1, SIGM l2 s2 a2) -> case (combAnns a1 a2) of 
    Just a -> SIGM l1 s1 a
    _      -> STOP
  (ENUM l1 s1 b1 d1 a1, ENUM l2 s2 b2 d2 a2) -> case (combAnns a1 a2) of 
    Just a -> ENUM l1 (s1 `union` s2) (b1 && b2) d1 a
    _      -> STOP
  (_, _)                               -> STOP
  where combAnns [] [] = Just []
        combAnns (Nothing:as) (b:bs)                  = do
          rest <- combAnns as bs
          Just $ b:rest
        combAnns (a:as) (Nothing:bs)                  = do
          rest <- combAnns as bs
          Just $ a:rest
        combAnns (Just a:as) (Just b:bs) | eql False d book a b = do
          rest <- combAnns as bs
          Just $ (Just a):rest
        combAnns _ _ = Nothing


-- Extracts variable names from eliminator/lambda branches
-- 1) Traverses i' layers deep to find lambda-bound names
--    When no lambda gives a name to the argument 
--    (i.e. it's implicit in a λ{..}), call it "$noname"
-- 2) Uses `j` to skip already-applied arguments when inside an (App f x) chain
-- 3) For multi-branch eliminators, combines names from all branches
--    3.1) When names conflict, prefers actual names over "$noname"
--    3.2) NatM/LstM/SigM need special handling for their argument counts
--
-- Returns: from          λp.s     , extracts ["p"] 
--          from  NatM z (λp.s)    , extracts ["$noname", "p"]
--          from (NatM z (λp.s)) x), extracts ["p"]
getVarNames :: Term -> [String] -> [String]
getVarNames term defs = go (length defs) 0 term [] defs
  where
    go :: Int -> Int -> Term -> [String] -> [String] -> [String]
    go 0 j term nams defs = nams
    -- go, not skipping the names of the arguments
    go i 0 term nams defs@(def:rest) = case cut term of
      App f x   -> go i 1 f nams defs
      Lam k _ b -> (k   : go (i-1) 0 (b (Var "_" 0)) nams rest)
      UniM f    -> (def : go (i-1) 0 f nams rest)
      BitM f t  -> (def : combine (go (i-1) 0 f nams rest) (go (i-1) 0 t nams rest) rest)
      NatM z s  -> (def : combine (go (i-1) 0 z nams rest) (go (i-1) 1 s nams rest) rest)
      LstM n c  -> (def : combine (go (i-1) 0 n nams rest) (go (i-1) 2 c nams rest) rest)
      EnuM c d  -> (def : go (i-1) 1 d nams rest)
      SigM g    -> (def : go (i-1) 2 g nams rest)
      EqlM f    -> (def : go (i-1) 0 f nams rest)
      _ -> defs
    -- go, but skip j arguments
    go i j term nams defs@(def:rest) = case cut term of
      App f x   -> go i (j+1) f nams defs
      Lam k _ b -> go i (j-1) (b (Var "_" 0)) nams defs
      UniM f    -> go i (j-1) f nams defs
      BitM f t  -> combine (go i (j-1) f nams defs) (go i (j-1)   t nams defs) defs
      NatM z s  -> combine (go i (j-1) z nams defs) (go i (j-1+1) s nams defs) defs
      LstM n c  -> combine (go i (j-1) n nams defs) (go i (j-1+2) c nams defs) defs
      EnuM c d  -> go i (j-1+1) d nams defs
      SigM g    -> go i (j-1+2) g nams defs
      EqlM f    -> go i (j-1) f nams defs
      _ -> defs
    go i j term nams [] = error "unreachable A" -- i > 0, no remaining defaults
    combine :: [String] -> [String] -> [String] -> [String]
    combine a b defs@(def:rest) = 
      case (a,b) of
      (a:as,b:bs) -> case (a,b) of
        (a,b) | a == def -> b:(combine as bs rest)
        (a,b)            -> a:(combine as bs rest)
      _           -> a
    combine [] [] [] = []
    combine a  b  [] = error "unreachable B" -- called with go without enough defaults


getAnnotations :: Int -> Book -> Term -> Maybe [Maybe Term]
getAnnotations d book term = case cut term of
  NatM _ s -> go d 1 0 s [] [Nothing]
  EnuM _ e -> go d 1 0 e [] [Nothing]
  LstM _ c -> go d 2 0 c [] [Nothing, Nothing]
  SigM g   -> go d 2 0 g [] [Nothing, Nothing]
  _ -> Nothing  -- or however you want to handle non-NatM cases
  where
    go :: Int -> Int -> Int -> Term -> [Maybe Term] -> [Maybe Term] -> Maybe [Maybe Term]
    go d 0 j term anns defs = Just anns
    -- go, not skipping the names of the arguments
    go d i 0 term anns defs@(def:rest) = case cut term of
      App f x   -> go d i 1 f anns defs
      Lam k t b -> do
        anns' <- go (d+1) (i-1) 0 (b (Var k d)) anns rest
        return (t : anns')
      UniM f    -> do
        anns' <- go d (i-1) 0 f anns rest
        return (Nothing : anns')
      BitM f t  -> do
        fAnns <- go d (i-1) 0 f anns rest
        tAnns <- go d (i-1) 0 t anns rest
        anns' <- combine fAnns tAnns rest
        return (Nothing : anns')
      NatM z s  -> do
        zAnns <- go d (i-1) 0 z anns rest
        sAnns <- go d (i-1) 1 s anns rest
        anns' <- combine zAnns sAnns rest
        return (Nothing : anns')
      LstM n c  -> do
        nAnns <- go d (i-1) 0 n anns rest
        cAnns <- go d (i-1) 2 c anns rest
        anns' <- combine nAnns cAnns rest
        return (Nothing : anns')
      EnuM c d' -> do
        anns' <- go d (i-1) 1 d' anns rest
        return (Nothing : anns')
      SigM g    -> do
        anns' <- go d (i-1) 2 g anns rest
        return (Nothing : anns')
      EqlM f    -> do
        anns' <- go d (i-1) 0 f anns rest
        return (Nothing : anns')
      _ -> Just defs
    -- go, but skip j arguments
    go d i j term anns defs@(def:rest) = case cut term of
      App f x   -> go d i (j+1) f anns defs
      Lam k _ b -> go (d+1) i (j-1) (b (Var k d)) anns defs
      UniM f    -> go d i (j-1) f anns defs
      BitM f t  -> do
        fAnns <- go d i (j-1) f anns defs
        tAnns <- go d i (j-1) t anns defs
        combine fAnns tAnns defs
      NatM z s  -> do
        zAnns <- go d i (j-1) z anns defs
        sAnns <- go d i (j-1+1) s anns defs
        combine zAnns sAnns defs
      LstM n c  -> do
        nAnns <- go d i (j-1) n anns defs
        cAnns <- go d i (j-1+2) c anns defs
        combine nAnns cAnns defs
      EnuM c d' -> go d i (j-1+1) d' anns defs
      SigM g    -> go d i (j-1+2) g anns defs
      EqlM f    -> go d i (j-1) f anns defs
      _ -> Just defs
    go d i j term nams [] = Nothing -- i > 0, no remaining defaults

    combine :: [Maybe Term] -> [Maybe Term] -> [Maybe Term] -> Maybe [Maybe Term]
    combine a b defs@(def:rest) = 
      case (a,b) of
        (Nothing:as,b:bs) -> do
          rest' <- combine as bs rest
          return (b : rest')
        (a:as,Nothing:bs) -> do
          rest' <- combine as bs rest
          return (a : rest')
        (Just a:as, Just b:bs) | eql False d book a b -> do
          rest' <- combine as bs rest
          return (Just a : rest')
        _ -> Nothing
    combine [] [] [] = Just []
    combine a b [] = Nothing -- called with go without enough defaults




