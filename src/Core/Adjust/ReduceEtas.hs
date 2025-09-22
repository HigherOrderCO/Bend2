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
--        λ{A(a1,..):tA_1[x,a1..]; ..; B(b1,..): tB_1[x,a1..]; ..}(x),
--        λ{A(a1,..):tA_2[x,a1..]; ..; B(b1,..): tB_2[x.a1..]; ..}(x),
--   ...] 
--  ------------------------------------------------------------------- reduceEtas
--  λ{
--    A: t[
--          tA_1[A(a1,a2,..), a1..]],
--          tA_2[A(a1,a2,..), a1..]],
--     ...];
--    B: t[
--          tB_1[x ~> B(b1,b2,..)]],
--          tB_2[x ~> B(b1,b2,..)]],
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
--               then return a label encoding which kinda of λ{..}.
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

-- Main eta-reduction function
-- 1) Assumes the `term` at call time is completely in HOAS bind form.
--    Otherwise, (f Var nam d) is not useful, and variable capture/shadowing can happen.
-- 2) Uses bindVarByName for the reconstructions x ~> A(a1,a2,..) and rebindings (after (f (Var nam d)) destroyed them)
--    bindVarByIndex/Name is blind to `d`, hence the use of unique `nam`
-- 3) Receives the eliminator type and var names a1.. from isEtaLong
-- 5) Rewrites the subterms using resolveMatches
--
-- Returns  : term in the form λ{A(a1..):λ{B:..}; ..}
-- Important: this does not changes `SupM` eliminators.
reduceEtas :: Int -> Span -> Term -> Term
reduceEtas d span (Loc l term) = reduceEtas d l term
reduceEtas d span term = case term of
  Lam k mty f ->
      -- The "$" prefix ensures `nam` won't clash with user variables
      let nam = "$"++show d in
      case isEtaLong d span nam (f (Var nam d)) of
        EMPM -> EmpM
        EQLM -> EqlM refl 
            where
            refl = reduceEtas d span $ bindVarByName nam Rfl (resolveMatches span nam EQLM 0 "" [] (f (Var nam d)))
        UNIM -> UniM u 
            where
            u    = reduceEtas d span $ bindVarByName nam One (resolveMatches span nam UNIM 0 "" [] (f (Var nam d)))
        BITM -> BitM fl tr 
            where
            fl   = reduceEtas d span $ bindVarByName nam Bt0 (resolveMatches span nam BITM 0 "" [] (f (Var nam d)))
            tr   = reduceEtas d span $ bindVarByName nam Bt1 (resolveMatches span nam BITM 1 "" [] (f (Var nam d)))
        NATM nams@[p] -> NatM z s 
            where
            z    = reduceEtas d span $ bindVarByName nam Zer (resolveMatches span nam (NATM [p]) 0 "" [] (f (Var nam d)))
            s    = reduceEtas d span $ (Lam p (Just Nat) (\q -> 
                                       bindVarByName nam (Suc q) (resolveMatches span nam (NATM nams) 1 "" [Sub q] (f (Var nam d)))))
        LSTM nams@[h,t] -> LstM nil cons 
            where
            nil  = reduceEtas d span $ bindVarByName nam Nil (resolveMatches span nam (LSTM nams) 0 "" [] (f (Var nam d)))
            cons = reduceEtas d span $ (Lam h Nothing (\h ->
                                        Lam t Nothing (\t ->
                                       bindVarByName nam (Con h t) (resolveMatches span nam (LSTM nams) 1 "" [Sub h, Sub t] (f (Var nam d))))))
        SIGM nams@[a,b] -> SigM pair
            where
            pair = reduceEtas d span $ (Lam a Nothing (\a ->
                                        Lam b Nothing (\b ->
                                       bindVarByName nam (Tup a b) (resolveMatches span nam (SIGM nams) 0 "" [Sub a, Sub b] (f (Var nam d))))))
        ENUM syms compl nams@[de] -> EnuM cases def 
          where
          cases = map (\sym -> (sym, reduceEtas d span $ bindVarByName nam (Sym sym) (resolveMatches span nam (ENUM syms compl nams) 0 sym [] (f (Var nam d))))) syms
          def = if compl
                then reduceEtas d span (Lam de Nothing (\q -> bindVarByName nam q (resolveMatches span nam (ENUM syms compl nams) (-1) "" [Sub q] (f (Var nam d)))))
                else One
        _ -> Lam k mty (\x -> reduceEtas (d+1) span (f x))
        -- SUPM lab -> not reduced
  Var n i       -> Var n i
  Ref n i       -> Ref n i
  Sub t'        -> Sub t'
  Fix n f       -> Fix n (\v -> reduceEtas (d+1) span (f v))
  Let n mty v f -> Let n (fmap (reduceEtas d span) mty) (reduceEtas d span v) (\v' -> reduceEtas (d+1) span (f v'))
  Use n v f     -> Use n (reduceEtas d span v) (\v' -> reduceEtas (d+1) span (f v'))
  Set           -> Set
  Chk t' ty     -> Chk (reduceEtas d span t') (reduceEtas d span ty)
  Emp           -> Emp
  EmpM          -> EmpM
  Uni           -> Uni
  One           -> One
  UniM f        -> UniM (reduceEtas d span f)
  Bit           -> Bit
  Bt0           -> Bt0
  Bt1           -> Bt1
  BitM f g      -> BitM (reduceEtas d span f) (reduceEtas d span g)
  Nat           -> Nat
  Zer           -> Zer
  Suc t'        -> Suc (reduceEtas d span t')
  NatM z s      -> NatM (reduceEtas d span z) (reduceEtas d span s)
  Lst ty        -> Lst (reduceEtas d span ty)
  Nil           -> Nil
  Con h t'      -> Con (reduceEtas d span h) (reduceEtas d span t')
  LstM nil c    -> LstM (reduceEtas d span nil) (reduceEtas d span c)
  Enu ss        -> Enu ss
  Sym s         -> Sym s
  EnuM cs def   -> EnuM [(s, reduceEtas d span v) | (s,v) <- cs] (reduceEtas d span def)
  Num nt        -> Num nt
  Val nv        -> Val nv
  Op2 o a b     -> Op2 o (reduceEtas d span a) (reduceEtas d span b)
  Op1 o a       -> Op1 o (reduceEtas d span a)
  Sig a b       -> Sig (reduceEtas d span a) (reduceEtas d span b)
  Tup a b       -> Tup (reduceEtas d span a) (reduceEtas d span b)
  SigM f        -> SigM (reduceEtas d span f)
  All a b       -> All (reduceEtas d span a) (reduceEtas d span b)
  App f x       -> App (reduceEtas d span f) (reduceEtas d span x)
  Eql ty a b    -> Eql (reduceEtas d span ty) (reduceEtas d span a) (reduceEtas d span b)
  Rfl           -> Rfl
  EqlM f        -> EqlM (reduceEtas d span f)
  Rwt e f       -> Rwt (reduceEtas d span e) (reduceEtas d span f)
  Met n ty args -> Met n (reduceEtas d span ty) (map (reduceEtas d span) args)
  Era           -> Era
  Sup l a b     -> Sup (reduceEtas d span l) (reduceEtas d span a) (reduceEtas d span b)
  SupM l f      -> SupM (reduceEtas d span l) (reduceEtas d span f)
--Loc s t'      -> Loc s (reduceEtas d span t')
  Log s x       -> Log (reduceEtas d span s) (reduceEtas d span x)
  Pri p         -> Pri p
  Pat ss ms cs  -> Pat (map (reduceEtas d span) ss) [(k, reduceEtas d span v) | (k,v) <- ms] [(map (reduceEtas d span) ps, reduceEtas d span rhs) | (ps,rhs) <- cs]
  Frk l a b     -> Frk (reduceEtas d span l) (reduceEtas d span a) (reduceEtas d span b)
  Tst x         -> Tst (reduceEtas d span x)

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
resolveMatches span nam elim clause sym args (Loc span' term) = resolveMatches span' nam elim clause sym args term
resolveMatches span nam elim clause sym args t = case t of
  App f x      ->
    case cut x of
      (Var k i) -> if k == nam
        then case (cut f, elim, args) of
          (UniM u       , UNIM      , [])    -> resolveMatches span nam elim clause sym args $ u
          (BitM fl tr   , BITM      , [])    -> resolveMatches span nam elim clause sym args $ ([fl, tr] !! clause)
          (NatM z s     , NATM _    , [])    -> resolveMatches span nam elim clause sym args $ z
          (NatM z s     , NATM _    , [p])   -> resolveMatches span nam elim clause sym args $ appInnerArg 0 (getSpan span s) s p
          (EmpM         , EMPM      , [])    -> resolveMatches span nam elim clause sym args EmpM
          (LstM nil cons, LSTM _    , [])    -> resolveMatches span nam elim clause sym args $ nil
          (LstM nil cons, LSTM _    , [h,t]) -> resolveMatches span nam elim clause sym args $ appInnerArg 0 (getSpan span cons)  
                                                                                                 (appInnerArg 1 (getSpan span cons) cons t) h
          (SigM pair    , SIGM _    , [a,b]) -> resolveMatches span nam elim clause sym args $ appInnerArg 0 (getSpan span pair)
                                                                                                 (appInnerArg 1 (getSpan span pair) pair b) a
          (EqlM refl    , EQLM      , [])    -> resolveMatches span nam elim clause sym args refl
          (EnuM cs def  , ENUM _ _ _, [q])   -> resolveMatches span nam elim clause sym args $ appInnerArg 0 (getSpan span def) def q
          (EnuM cs def  , ENUM _ _ _, [])    -> case lookup sym cs of
                                Just branch  -> resolveMatches span nam elim clause sym args $ branch
                                Nothing      -> resolveMatches span nam elim clause sym args $ appInnerArg 0 (getSpan span def) def (Var k i)
          _ -> App (resolveMatches span nam elim clause sym args f) (resolveMatches span nam elim clause sym args x)
        else   App (resolveMatches span nam elim clause sym args f) (resolveMatches span nam elim clause sym args x)
      _     -> App (resolveMatches span nam elim clause sym args f) (resolveMatches span nam elim clause sym args x)
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
--Loc span t'  -> Loc span (resolveMatches span nam l clause sym args t')
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
--
-- Returns: from λx. (λ{0:Z; S:...}(x), λ{0:W; S:...}(x)) 
-- the label NATM [pred_name_from_S]
isEtaLong :: Int -> Span -> Name -> Term -> ElimLabel
isEtaLong d span nam (Loc spa t) = isEtaLong d spa nam t
isEtaLong d span nam t = case t of
  Lam k _ f   -> if k == nam then NONE else isEtaLong (d+1) span nam (f (Var k d))
  App f x     ->
    case cut x of
      (Var k _) -> if k == nam
        then
          case cut f of
       -- SupM l _    -> not eliminated
          EqlM _      -> EQLM <+> isEtaLong d span nam f
          EmpM        -> EMPM <+> isEtaLong d span nam f
          UniM _      -> UNIM <+> isEtaLong d span nam f
          BitM _ _    -> BITM <+> isEtaLong d span nam f
          NatM _ s    -> NATM (getVarNames 1 (getSpan span s) s) <+> isEtaLong d span nam f
          LstM _ c    -> LSTM (getVarNames 2 (getSpan span c) c) <+> isEtaLong d span nam f
          SigM g      -> SIGM (getVarNames 2 (getSpan span g) g) <+> isEtaLong d span nam f
          EnuM cs def -> (ENUM (map fst cs) (isLam def) (getVarNames 1 span def)) <+> isEtaLong d span nam f
          _           -> isEtaLong d span nam f
        else
            isEtaLong d span nam f <+> isEtaLong d span nam x
      _ -> isEtaLong d span nam f <+> isEtaLong d span nam x
  Var _ _     -> NONE
  Ref _ _     -> NONE
  Sub t'      -> isEtaLong d span nam t'
  Fix k f     -> isEtaLong (d+1) span nam (f (Var k d))
  Let k t v f -> let def = isEtaLong d span nam v <+> isEtaLong (d+1) span nam (f (Var k d)) in fromMaybe def (fmap (\typ -> def <+> isEtaLong d span nam typ) t)
  Use k v f   -> isEtaLong d span nam v <+> isEtaLong (d+1) span nam (f (Var k d))
  Set         -> NONE
  Chk t' ty   -> isEtaLong d span nam t' <+> isEtaLong d span nam ty
  Emp         -> NONE
  EmpM        -> NONE
  Uni         -> NONE
  One         -> NONE
  UniM f      -> isEtaLong d span nam f
  Bit         -> NONE
  Bt0         -> NONE
  Bt1         -> NONE
  BitM f g    -> isEtaLong d span nam f <+> isEtaLong d span nam g
  Nat         -> NONE
  Zer         -> NONE
  Suc t'      -> isEtaLong d span nam t'
  NatM z s    -> isEtaLong d span nam z <+> isEtaLong d span nam s
  Lst ty      -> isEtaLong d span nam ty
  Nil         -> NONE
  Con h t'    -> isEtaLong d span nam h <+> isEtaLong d span nam t'
  LstM nil c  -> isEtaLong d span nam nil <+> isEtaLong d span nam c
  Enu _       -> NONE
  Sym _       -> NONE
  EnuM cs def -> foldr (<+>) (isEtaLong d span nam def) (map (isEtaLong d span nam . snd) cs)
  Num _       -> NONE
  Val _       -> NONE
  Op2 _ a b   -> isEtaLong d span nam a <+> isEtaLong d span nam b
  Op1 _ a     -> isEtaLong d span nam a
  Sig a b     -> isEtaLong d span nam a <+> isEtaLong d span nam b
  Tup a b     -> isEtaLong d span nam a <+> isEtaLong d span nam b
  SigM f      -> isEtaLong d span nam f
  All a b     -> isEtaLong d span nam a <+> isEtaLong d span nam b
  Eql ty a b  -> isEtaLong d span nam ty <+> isEtaLong d span nam a <+> isEtaLong d span nam b
  Rfl         -> NONE
  EqlM f      -> isEtaLong d span nam f
  Rwt e f     -> isEtaLong d span nam e <+> isEtaLong d span nam f
  Met _ ty cx -> isEtaLong d span nam ty <+> foldr (<+>) NONE (map (isEtaLong d span nam) cx)
  Era         -> NONE
  Sup l a b   -> isEtaLong d span nam l <+> isEtaLong d span nam a <+> isEtaLong d span nam b
  SupM l f    -> isEtaLong d span nam l <+> isEtaLong d span nam f
--Loc _ t'    -> isEtaLong d span nam t'
  Log s x     -> isEtaLong d span nam s <+> isEtaLong d span nam x
  Pri _       -> NONE
  Pat ss ms cs -> foldr (<+>) NONE (map (isEtaLong d span nam) ss ++ map (isEtaLong d span nam . snd) ms ++ concatMap (\(ps, rhs) -> map (isEtaLong d span nam) ps ++ [isEtaLong d span nam rhs]) cs)
  Frk l a b   -> isEtaLong d span nam l <+> isEtaLong d span nam a <+> isEtaLong d span nam b
  Tst x       -> isEtaLong d span nam x

-- Auxiliary definitions / Utils
-- ------------------------------

-- SUPM not reduced
data ElimLabel
  = UNIM
  | BITM
  | NATM [String]               -- [predName]
  | EMPM
  | LSTM [String]               -- [headName,tailName]
  | SIGM [String]               -- [fstName , sndName]
  | EQLM
  | ENUM [String] Bool [String] -- [symbolNames], isNotComplete, [defaultArgName]
  | NONE
  deriving Show -- SUPM not reduced

-- Combines eliminator labels from multiple λ{..}(nam) occurrences
-- 1) NONE acts as identity: anything combined with NONE stays unchanged
-- 2) Same eliminator types combine by keeping first's parameters (NATM s1 <+> NATM s2 = NATM s1)
-- 3) Different eliminator types cancel to NONE (mixed patterns can't be eta-reduced)
-- 4) ENUMs merge their symbol lists and conjoin their completeness flags
--
-- Returns: NATM [p] <+> NATM [q] -> NATM [p]
--          NATM [p] <+> BITM      -> NONE
(<+>) :: ElimLabel -> ElimLabel -> ElimLabel
NONE          <+> x             = x
x             <+> NONE          = x
UNIM          <+> UNIM          = UNIM
BITM          <+> BITM          = BITM
NATM s1       <+> NATM s2       = NATM s1
EMPM          <+> EMPM          = EMPM
LSTM s1       <+> LSTM s2       = LSTM s1
SIGM s1       <+> SIGM s2       = SIGM s1
EQLM          <+> EQLM          = EQLM
ENUM s1 b1 d1 <+> ENUM s2 b2 d2 = ENUM (s1 `union` s2) (b1 && b2) d1
_             <+> _             = NONE

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
getVarNames :: Int -> Span -> Term -> [String]
getVarNames i' span term = go i' 0 term []
  where
    def = "$noname"
    combine :: [String] -> [String] -> [String]
    combine a b = 
      case (a,b) of
      (a:as,b:bs) -> case (a,b) of
        (a,b) | a == def -> b:(combine as bs)
        (a,b)            -> a:(combine as bs)
      _           -> a
    -- go, but skip j arguments
    go :: Int -> Int -> Term -> [String] -> [String]
    go 0 j term nams = nams
    go i j term nams | j > 0 = case cut term of
      App f x   -> go i j f nams
      Lam k _ b -> go i (j-1) (b (Var "_" 0)) nams
      UniM f    -> go i (j-1) f nams
      BitM f t  -> combine (go i (j-1) f nams) (go i (j-1) t nams)
      NatM z s  -> combine (go i (j-1) z nams) (go i (j-1+1) s nams)
      LstM n c  -> combine (go i (j-1) n nams) (go i (j-1+2) c nams)
      EnuM c d  -> go i (j-1+1) d nams
      SigM g    -> go i (j-1+2) g nams
      EqlM f    -> go i (j-1) f nams
      _ -> errorWithSpan span $ "Not enough arguments. Expected > " ++ show i' ++ ":"

    -- go, getting the names of the arguments
    go i 0 term nams = case cut term of
      App f x   -> go i 1 f nams
      Lam k _ b -> (k   : go (i-1) 0 (b (Var "_" 0)) nams)
      UniM f    -> (def : go (i-1) 0 f nams)
      BitM f t  -> (def : combine (go (i-1) 0 f nams) (go (i-1) 0 t nams))
      NatM z s  -> (def : combine (go (i-1) 0 z nams) (go (i-1) 1 s nams))
      LstM n c  -> (def : combine (go (i-1) 0 n nams) (go (i-1) 2 c nams))
      EnuM c d  -> (def : go (i-1) 1 d nams)
      SigM g    -> (def : go (i-1) 2 g nams)
      EqlM f    -> (def : go (i-1) 0 f nams)
      _ -> errorWithSpan span $ "Not enough arguments. Expected > " ++ show i' ++ ":"
    go i j term nams = -- j < 0, unreachable
           errorWithSpan span $ "Not enough arguments. Expected > " ++ show i' ++ ":"

-- Applies an argument deep inside nested eliminators/lambdas
-- 1) Parameter `i` counts how many eliminator layers to traverse
-- 2) When i=0, applies the current term to `arg'
-- 3) When i>0: descends into the eliminator's branches, adjusting for their arities
--    3.1) NatM's successor branch expects 1 extra arg, so skip it with adding one: (i-1+1)
--    3.2) LstM's cons branch expects 2 extra args, so skip it with adding two: (l-1+2)
--    3..) Same for SigM, and EnuM default
-- 4) App nodes increment `i` to track depth in the application spine
--
-- Returns: appInnerArg 0 0 span (λx.body) arg -> body[arg/x]
--          appInnerArg 1 0 span (NatM z (λp.s)) arg -> NatM (App z arg) (λp.s[p ~> arg])
appInnerArg :: Int -> Span -> Term -> Term -> Term
appInnerArg i span (Loc l t) arg = Loc l (appInnerArg i span t arg)
-- jymp over applied functions
appInnerArg i span (App f x) arg = App (appInnerArg (i+1) span f arg) x
-- reduce lambdas
appInnerArg 0 span (Lam _ _ b) arg = b arg
-- apply non-lambdas
appInnerArg 0 span func arg = App func arg
-- go deeper for the next eliminator
appInnerArg i span func arg = case func of
  Lam k mt b  -> Lam k mt (\x -> appInnerArg (i-1) span (b x) arg) 
  EmpM        -> EmpM
  EqlM f      -> EqlM (appInnerArg (i-1) span f arg)
  UniM f      -> UniM (appInnerArg (i-1) span f arg) 
  BitM f t    -> BitM (appInnerArg (i-1) span f arg) (appInnerArg (i-1) span t arg)
  NatM z s    -> NatM (appInnerArg (i-1) span z arg) (appInnerArg (i-1+1) span s arg)
  LstM n c    -> LstM (appInnerArg (i-1) span n arg) (appInnerArg (i-1+2) span c arg)
  SigM g      -> SigM (appInnerArg (i-1+2) span g arg)
  EnuM cs def -> EnuM (map (\(s,t) -> (s, appInnerArg (i-1) span t arg)) cs) (appInnerArg (i-1+1) span def arg)
  _                     -> errorWithSpan span $ "Not enough arguments."

