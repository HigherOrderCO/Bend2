{-./../Type.hs-}

-- Eta-Form
-- ========
--
-- This module performs eta-reduction with lambda-inject optimization, transforming
-- nested lambda-match patterns into more efficient forms.
--
-- Basic Transformation:
-- --------------------
-- λx. λy. λz. (λ{...} x) ~> λ{0n:λy.λz.A; 1n+:λy.λz.B}
--
-- The optimization moves intermediate lambdas inside match branches. It also handles
-- passthrough constructs (Let, Use, Chk, Loc, Log, App) and reconstructs the scrutinee
-- when needed using 'use' bindings.
--
-- Examples:
-- ---------
-- 1. Simple eta-reduction:
--    λn. (λ{0n:Z; 1n+:S} n) ~> λ{0n:Z; 1n+:S}
--
-- 2. With intermediate lambdas:
--    λa. λb. (λ{0n:Z; 1n+:S} a) ~> λ{0n:λb.Z; 1n+:λp.λb.S}
--
-- 3. With scrutinee reconstruction:
--    λa. (λ{0n:a; 1n+:λp. 1n+p} a) ~> λ{0n:use a=0n a; 1n+:λp. use a=1n+p 1n+p}
--
-- 4. Reconstruction disabled when field name matches scrutinee:
--    λb. (λ{0n:Z; 1n+:λb. S} b) ~> λ{0n:use b=0n Z; 1n+:λb. S} (no reconstruction in 1n+ case)
--
-- Key Points:
-- ----------
-- - Field lambdas are injected first, then intermediate constructs
-- - Scrutinee is reconstructed with 'use' bindings unless field names conflict
-- - Handles Let, Use, Chk, Loc, Log, and App as passthrough constructs

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

-- Auxiliary definitions / Utils
--
data ElimLabel
  = UNIM
  | BITM
  | NATM [String]
  | EMPM
  | LSTM [String]
  | SIGM [String]
  | EQLM
  | ENUM [String] Bool [String]
  | NONE
  -- | SUPM Term
  deriving Show

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
-- SUPM t1    <+> SUPM t2 | equal 0 (Book M.empty []) t1 t2 = SUPM t1

-- Main eta-reduction function
--
reduceEtas :: Int -> Term -> Term
reduceEtas d term = reduceEtasGo d (getSpan noSpan term) term

reduceEtasGo :: Int -> Span -> Term -> Term
reduceEtasGo d span (Loc l term) = reduceEtasGo d l term
reduceEtasGo d span term = case term of
-- this assumes `t` is bound, because without this we can't (at least not easily) replace a var that is originally
-- an argument of a constructor in a match by a var of the newly-pulled-outward match of the reduction
  Lam k mty f ->
      let nam = "$"++show d in -- bindVarByName effectively counts depth starting from 0, so neither `k` nor `d` are enough to single out this var
      case isEtaLong d span nam (f (Var nam d)) of
        EMPM -> EmpM

        EQLM -> EqlM refl where
            refl = reduceEtasGo d span $ bindVarByName nam Rfl (resolveMatches d span nam EQLM 0 "" [] (f (Var nam d)))

        UNIM -> UniM u where
            u = reduceEtasGo d span $ bindVarByName nam One (resolveMatches d span nam UNIM 0 "" [] (f (Var nam d)))
                                                                                              -- if we don't use f (Var nam d), 
                                                                                              -- then the recursive reduceEtasGo
                                                                                              -- won't know that it has found
                                                                                              -- a deeper app-lam-match on k
        BITM -> BitM fl tr where
            fl = reduceEtasGo d span $ bindVarByName nam Bt0 (resolveMatches d span nam BITM 0 "" [] (f (Var nam d)))
            tr = reduceEtasGo d span $ bindVarByName nam Bt1 (resolveMatches d span nam BITM 1 "" [] (f (Var nam d)))

        NATM nams@[p] -> NatM z s where
            z = reduceEtasGo d span $ bindVarByName nam Zer (resolveMatches d span nam (NATM [p]) 0 "" [] (f (Var nam d)))
            s = reduceEtasGo d span (Lam p (Just Nat) (\q -> bindVarByName nam (Suc q) (resolveMatches (d+1) span nam (NATM nams) 1 "" [Sub q] (f (Var nam d)))))

        LSTM nams@[h,t] -> LstM nil cons where
            nil  = reduceEtasGo d span $ bindVarByName nam Nil (resolveMatches d span nam (LSTM nams) 0 "" [] (f (Var nam d)))
            cons = reduceEtasGo d span (Lam h Nothing (\h ->
                                 Lam t Nothing (\t ->
                                 bindVarByName nam (Con h t) (resolveMatches (d+2) span nam (LSTM nams) 1 "" [Sub h, Sub t] (f (Var nam d))))))

        SIGM nams@[a,b] -> SigM pair where
            pair = reduceEtasGo d span (Lam a Nothing (\a ->
                                 Lam b Nothing (\b ->
                                 bindVarByName nam (Tup a b) (resolveMatches (d+2) span nam (SIGM nams) 0 "" [Sub a, Sub b] (f (Var nam d))))))

        ENUM syms compl nams@[de] -> EnuM cases def where
          cases = map (\sym -> (sym, reduceEtasGo d span $ bindVarByName nam (Sym sym) (resolveMatches d span nam (ENUM syms compl nams) 0 sym [] (f (Var nam d))))) syms
          def = if compl
              then reduceEtasGo d span (Lam de Nothing (\q -> bindVarByName nam q (resolveMatches (d+1) span nam (ENUM syms compl nams) (-1) "" [Sub q] (f (Var nam d)))))
              else One
        
        -- SUPM lab -> undefined

        _ -> Lam k mty (\x -> reduceEtasGo (d+1) span (f x))

  -- Not a Lam, just propagate deeper
  Var n i       -> Var n i
  Ref n i       -> Ref n i
  Sub t'        -> Sub t'
  Fix n f       -> Fix n (\v -> reduceEtasGo (d+1) span (f v))
  Let n mty v f -> Let n (fmap (reduceEtasGo d span) mty) (reduceEtasGo d span v) (\v' -> reduceEtasGo (d+1) span (f v'))
  Use n v f     -> Use n (reduceEtasGo d span v) (\v' -> reduceEtasGo (d+1) span (f v'))
  Set           -> Set
  Chk t' ty     -> Chk (reduceEtasGo d span t') (reduceEtasGo d span ty)
  Emp           -> Emp
  EmpM          -> EmpM
  Uni           -> Uni
  One           -> One
  UniM f        -> UniM (reduceEtasGo d span f)
  Bit           -> Bit
  Bt0           -> Bt0
  Bt1           -> Bt1
  BitM f g      -> BitM (reduceEtasGo d span f) (reduceEtasGo d span g)
  Nat           -> Nat
  Zer           -> Zer
  Suc t'        -> Suc (reduceEtasGo d span t')
  NatM z s      -> NatM (reduceEtasGo d span z) (reduceEtasGo d span s)
  Lst ty        -> Lst (reduceEtasGo d span ty)
  Nil           -> Nil
  Con h t'      -> Con (reduceEtasGo d span h) (reduceEtasGo d span t')
  LstM nil c    -> LstM (reduceEtasGo d span nil) (reduceEtasGo d span c)
  Enu ss        -> Enu ss
  Sym s         -> Sym s
  EnuM cs def   -> EnuM [(s, reduceEtasGo d span v) | (s,v) <- cs] (reduceEtasGo d span def)
  Num nt        -> Num nt
  Val nv        -> Val nv
  Op2 o a b     -> Op2 o (reduceEtasGo d span a) (reduceEtasGo d span b)
  Op1 o a       -> Op1 o (reduceEtasGo d span a)
  Sig a b       -> Sig (reduceEtasGo d span a) (reduceEtasGo d span b)
  Tup a b       -> Tup (reduceEtasGo d span a) (reduceEtasGo d span b)
  SigM f        -> SigM (reduceEtasGo d span f)
  All a b       -> All (reduceEtasGo d span a) (reduceEtasGo d span b)
  App f x       -> App (reduceEtasGo d span f) (reduceEtasGo d span x)
  Eql ty a b    -> Eql (reduceEtasGo d span ty) (reduceEtasGo d span a) (reduceEtasGo d span b)
  Rfl           -> Rfl
  EqlM f        -> EqlM (reduceEtasGo d span f)
  Rwt e f       -> Rwt (reduceEtasGo d span e) (reduceEtasGo d span f)
  Met n ty args -> Met n (reduceEtasGo d span ty) (map (reduceEtasGo d span) args)
  Era           -> Era
  Sup l a b     -> Sup (reduceEtasGo d span l) (reduceEtasGo d span a) (reduceEtasGo d span b)
  SupM l f      -> SupM (reduceEtasGo d span l) (reduceEtasGo d span f)
  -- Loc s t'      -> Loc s (reduceEtasGo d span t')
  Log s x       -> Log (reduceEtasGo d span s) (reduceEtasGo d span x)
  Pri p         -> Pri p
  Pat ss ms cs  -> Pat (map (reduceEtasGo d span) ss) [(k, reduceEtasGo d span v) | (k,v) <- ms] [(map (reduceEtasGo d span) ps, reduceEtasGo d span rhs) | (ps,rhs) <- cs]
  Frk l a b     -> Frk (reduceEtasGo d span l) (reduceEtasGo d span a) (reduceEtasGo d span b)
  Tst x         -> Tst (reduceEtasGo d span x)

-- Updated resolveMatches that takes a list of arguments
resolveMatches :: Int -> Span -> Name -> ElimLabel -> Int -> String -> [Term] -> Term -> Term
resolveMatches d span nam l clause sym args (Loc span' term) = resolveMatches d span' nam l clause sym args term
resolveMatches d span nam l clause sym args t = case t of
  App f x      ->
    case cut x of
      (Var k i) -> if k == nam
        then case (cut f, l, args) of
          -- Unit matches
          (UniM u,     UNIM, [])  -> resolveMatches d span nam l clause sym args $ u
          -- Bit matches
          (BitM fl tr, BITM, [])  -> resolveMatches d span nam l clause sym args $ ([fl, tr] !! clause)
          -- Nat matches
          (NatM z s, NATM _, [])  -> resolveMatches d span nam l clause sym args $ z
          (NatM z s, NATM _, [p]) -> resolveMatches d span nam l clause sym args $ appInnerArg 0 0 (getSpan span s) s p

          -- Empty matches
          (EmpM, EMPM, []) -> resolveMatches d span nam l clause sym args EmpM
          
          -- List matches
          (LstM nil cons, LSTM _, [])    -> resolveMatches d span nam l clause sym args $ nil
          (LstM nil cons, LSTM _, [h,t]) -> resolveMatches d span nam l clause sym args $ appInnerArg 0 0 (getSpan span cons)(appInnerArg 1 0 (getSpan span cons) cons t) h
         
          -- Pair matches
          (SigM pair, SIGM _, [a,b]) -> resolveMatches d span nam l clause sym args $ appInnerArg 0 0 (getSpan span pair)(appInnerArg 1 0 (getSpan span pair) pair b) a
          
          -- Equality matches
          (EqlM refl, EQLM, []) -> resolveMatches d span nam l clause sym args refl

          -- Enum matches
          (EnuM cs def, ENUM _ _ _, [q]) -> resolveMatches d span nam l clause sym args $ appInnerArg 0 0 (getSpan span def) def q
          (EnuM cs def, ENUM _ _ _, [])  -> case lookup sym cs of
              Just branch                -> resolveMatches d span nam l clause sym args $ branch
              Nothing                    -> resolveMatches d span nam l clause sym args $ appInnerArg 0 0 (getSpan span def) def (Var k i)
          
          -- Not an eliminator application
          _ -> App (resolveMatches d span nam l clause sym args f) (resolveMatches d span nam l clause sym args x)
        else App (resolveMatches d span nam l clause sym args f) (resolveMatches d span nam l clause sym args x)
      _         -> App (resolveMatches d span nam l clause sym args f) (resolveMatches d span nam l clause sym args x)

  -- Not an eliminator application, just propagate deeper
  Lam k ty f   -> Lam k (fmap (resolveMatches d span nam l clause sym args) ty) (\x -> resolveMatches (d+1) span nam l clause sym args (f x))
  Var k i      -> Var k i
  Ref k i      -> Ref k i
  Sub t'       -> Sub (resolveMatches d span nam l clause sym args t')
  Fix k f      -> Fix k (\x -> resolveMatches (d+1) span nam l clause sym args (f x))
  Let k ty v f -> Let k (fmap (resolveMatches d span nam l clause sym args) ty) (resolveMatches d span nam l clause sym args v) (\x -> resolveMatches (d+1) span nam l clause sym args (f x))
  Use k v f    -> Use k (resolveMatches d span nam l clause sym args v) (\x -> resolveMatches (d+1) span nam l clause sym args (f x))
  Set          -> Set
  Chk t' ty    -> Chk (resolveMatches d span nam l clause sym args t') (resolveMatches d span nam l clause sym args ty)
  Emp          -> Emp
  EmpM         -> EmpM
  Uni          -> Uni
  One          -> One
  UniM f       -> UniM (resolveMatches d span nam l clause sym args f)
  Bit          -> Bit
  Bt0          -> Bt0
  Bt1          -> Bt1
  BitM f g     -> BitM (resolveMatches d span nam l clause sym args f) (resolveMatches d span nam l clause sym args g)
  Nat          -> Nat
  Zer          -> Zer
  Suc t'       -> Suc (resolveMatches d span nam l clause sym args t')
  NatM z s     -> NatM (resolveMatches d span nam l clause sym args z) (resolveMatches d span nam l clause sym args s)
  Lst ty       -> Lst (resolveMatches d span nam l clause sym args ty)
  Nil          -> Nil
  Con h t'     -> Con (resolveMatches d span nam l clause sym args h) (resolveMatches d span nam l clause sym args t')
  LstM nil c   -> LstM (resolveMatches d span nam l clause sym args nil) (resolveMatches d span nam l clause sym args c)
  Enu syms     -> Enu syms
  Sym s        -> Sym s
  EnuM cs def  -> EnuM (map (\(s,t') -> (s, resolveMatches d span nam l clause sym args t')) cs) (resolveMatches d span nam l clause sym args def)
  Num typ      -> Num typ
  Val v        -> Val v
  Op2 op a b   -> Op2 op (resolveMatches d span nam l clause sym args a) (resolveMatches d span nam l clause sym args b)
  Op1 op a     -> Op1 op (resolveMatches d span nam l clause sym args a)
  Sig a b      -> Sig (resolveMatches d span nam l clause sym args a) (resolveMatches d span nam l clause sym args b)
  Tup a b      -> Tup (resolveMatches d span nam l clause sym args a) (resolveMatches d span nam l clause sym args b)
  SigM f       -> SigM (resolveMatches d span nam l clause sym args f)
  All a b      -> All (resolveMatches d span nam l clause sym args a) (resolveMatches d span nam l clause sym args b)
  Eql ty a b   -> Eql (resolveMatches d span nam l clause sym args ty) (resolveMatches d span nam l clause sym args a) (resolveMatches d span nam l clause sym args b)
  Rfl          -> Rfl
  EqlM f       -> EqlM (resolveMatches d span nam l clause sym args f)
  Rwt e f      -> Rwt (resolveMatches d span nam l clause sym args e) (resolveMatches d span nam l clause sym args f)
  Met name ty as -> Met name (resolveMatches d span nam l clause sym args ty) (map (resolveMatches d span nam l clause sym args) as)
  Era          -> Era
  Sup l' a b   -> Sup (resolveMatches d span nam l clause sym args l') (resolveMatches d span nam l clause sym args a) (resolveMatches d span nam l clause sym args b)
  SupM l' f    -> SupM (resolveMatches d span nam l clause sym args l') (resolveMatches d span nam l clause sym args f)
  -- Loc span t'  -> Loc span (resolveMatches d span nam l clause sym args t')
  Log s x      -> Log (resolveMatches d span nam l clause sym args s) (resolveMatches d span nam l clause sym args x)
  Pri pf       -> Pri pf
  Pat ss ms cs -> Pat (map (resolveMatches d span nam l clause sym args) ss)
                      (map (\(m,t') -> (m, resolveMatches d span nam l clause sym args t')) ms)
                      (map (\(ps,rhs) -> (map (resolveMatches d span nam l clause sym args) ps, resolveMatches d span nam l clause sym args rhs)) cs)
  Frk l' a b   -> Frk (resolveMatches d span nam l clause sym args l') 
                      (resolveMatches d span nam l clause sym args a) 
                      (resolveMatches d span nam l clause sym args b)
  Tst x        -> Tst (resolveMatches d span nam l clause sym args x)

appInnerArg :: Int -> Int -> Span -> Term -> Term -> Term
-- reduce lambdas
appInnerArg i j span (Loc l t) arg = Loc l (appInnerArg i j span t arg)
appInnerArg i j span (App f x) arg = App (appInnerArg (i+1) j span f arg) x
appInnerArg 0 0 span (Lam _ _ b) arg = b arg
-- apply non-lambdas
appInnerArg 0 0 span func arg = App func arg
-- go deeper for the next eliminator
appInnerArg l 0 span func arg = case func of
  Lam k mt b  -> Lam k mt (\x -> appInnerArg (l-1) 0 span (b x) arg) 
  EmpM        -> EmpM
  EqlM f      -> EqlM (appInnerArg (l-1) 0 span f arg)
  UniM f      -> UniM (appInnerArg (l-1) 0 span f arg) 
  BitM f t    -> BitM (appInnerArg (l-1) 0 span f arg) (appInnerArg (l-1) 0 span t arg)
  NatM z s    -> NatM (appInnerArg (l-1) 0 span z arg) (appInnerArg (l-1+1) 0 span s arg)
  LstM n c    -> LstM (appInnerArg (l-1) 0 span n arg) (appInnerArg (l-1+2) 0 span c arg)
  SigM g      -> SigM (appInnerArg (l-1+2) 0 span g arg)
  EnuM cs def -> EnuM (map (\(s,t) -> (s, appInnerArg (l-1) 0 span t arg)) cs) (appInnerArg (l-1+1) 0 span def arg)
  _                     -> errorWithSpan span $ "Not enough arguments."
appInnerArg _ _ span _ _ = errorWithSpan span $ "Not enough arguments."

-- Check if a term contains the eta-long pattern: App (λ{...}) (Var name)
isEtaLong :: Int -> Span -> Name -> Term -> ElimLabel
isEtaLong d span n t = case t of
  Lam k _ f   -> if k == n then NONE else isEtaLong (d+1) span n (f (Var k d))
  App f x     ->
    case cut x of
      (Var k _) -> if k == n
        then
          case cut f of
          UniM _      -> UNIM <+> isEtaLong d span n f
          BitM _ _    -> BITM <+> isEtaLong d span n f
          NatM _ s    -> NATM (getVarNames 1 span s) <+> isEtaLong d span n f
          EmpM        -> EMPM <+> isEtaLong d span n f
          LstM _ c    -> LSTM (getVarNames 2 (getSpan span c) c) <+> isEtaLong d span n f
          SigM g      -> SIGM (getVarNames 2 span g) <+> isEtaLong d span n f
          EqlM _      -> EQLM <+> isEtaLong d span n f
          -- SupM l _    -> SUPM l <+> isEtaLong d span n f
          EnuM cs def -> (ENUM (map fst cs) (isLam def) (getVarNames 1 span def)) <+> isEtaLong d span n f
          _           -> isEtaLong d span n f
        else
            isEtaLong d span n f <+> isEtaLong d span n x
      _ -> isEtaLong d span n f <+> isEtaLong d span n x
  Var _ _     -> NONE
  Ref _ _     -> NONE
  Sub t'      -> isEtaLong d span n t'
  Fix k f     -> isEtaLong (d+1) span n (f (Var k d))
  Let k t v f -> let def = isEtaLong d span n v <+> isEtaLong (d+1) span n (f (Var k d)) in fromMaybe def (fmap (\typ -> def <+> isEtaLong d span n typ) t)
  Use k v f   -> isEtaLong d span n v <+> isEtaLong (d+1) span n (f (Var k d))
  Set         -> NONE
  Chk t' ty   -> isEtaLong d span n t' <+> isEtaLong d span n ty
  Emp         -> NONE
  EmpM        -> NONE
  Uni         -> NONE
  One         -> NONE
  UniM f      -> isEtaLong d span n f
  Bit         -> NONE
  Bt0         -> NONE
  Bt1         -> NONE
  BitM f g    -> isEtaLong d span n f <+> isEtaLong d span n g
  Nat         -> NONE
  Zer         -> NONE
  Suc t'      -> isEtaLong d span n t'
  NatM z s    -> isEtaLong d span n z <+> isEtaLong d span n s
  Lst ty      -> isEtaLong d span n ty
  Nil         -> NONE
  Con h t'    -> isEtaLong d span n h <+> isEtaLong d span n t'
  LstM nil c  -> isEtaLong d span n nil <+> isEtaLong d span n c
  Enu _       -> NONE
  Sym _       -> NONE
  EnuM cs def -> foldr (<+>) (isEtaLong d span n def) (map (isEtaLong d span n . snd) cs)
  Num _       -> NONE
  Val _       -> NONE
  Op2 _ a b   -> isEtaLong d span n a <+> isEtaLong d span n b
  Op1 _ a     -> isEtaLong d span n a
  Sig a b     -> isEtaLong d span n a <+> isEtaLong d span n b
  Tup a b     -> isEtaLong d span n a <+> isEtaLong d span n b
  SigM f      -> isEtaLong d span n f
  All a b     -> isEtaLong d span n a <+> isEtaLong d span n b
  Eql ty a b  -> isEtaLong d span n ty <+> isEtaLong d span n a <+> isEtaLong d span n b
  Rfl         -> NONE
  EqlM f      -> isEtaLong d span n f
  Rwt e f     -> isEtaLong d span n e <+> isEtaLong d span n f
  Met _ ty cx -> isEtaLong d span n ty <+> foldr (<+>) NONE (map (isEtaLong d span n) cx)
  Era         -> NONE
  Sup l a b   -> isEtaLong d span n l <+> isEtaLong d span n a <+> isEtaLong d span n b
  SupM l f    -> isEtaLong d span n l <+> isEtaLong d span n f
  Loc _ t'    -> isEtaLong d span n t'
  Log s x     -> isEtaLong d span n s <+> isEtaLong d span n x
  Pri _       -> NONE
  Pat ss ms cs -> foldr (<+>) NONE (map (isEtaLong d span n) ss ++ map (isEtaLong d span n . snd) ms ++ concatMap (\(ps, rhs) -> map (isEtaLong d span n) ps ++ [isEtaLong d span n rhs]) cs)
  Frk l a b   -> isEtaLong d span n l <+> isEtaLong d span n a <+> isEtaLong d span n b
  Tst x       -> isEtaLong d span n x

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
      -- EmpM      -> 
      -- SupM f    ->
      _ -> errorWithSpan span $ "Not enough arguments. Expected > " ++ show i' ++ ":"
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
      -- EmpM      -> 
      -- SupM f    ->
      _ -> errorWithSpan span $ "Not enough arguments. Expected > " ++ show i' ++ ":"
    go i j term nams = -- j < 0
           errorWithSpan span $ "Not enough arguments. Expected > " ++ show i' ++ ":"
