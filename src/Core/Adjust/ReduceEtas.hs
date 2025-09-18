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
  | SUPM Term
  | EQLM
  | ENUM [String] Bool
  | NONE
  deriving Show

(<+>) :: ElimLabel -> ElimLabel -> ElimLabel
NONE <+> x    = x
x    <+> NONE = x
UNIM <+> UNIM = UNIM
BITM <+> BITM = BITM
NATM s1 <+> NATM s2 = NATM s1
EMPM <+> EMPM = EMPM
LSTM s1 <+> LSTM s2 = LSTM s1
SIGM s1 <+> SIGM s2 = SIGM s1
EQLM <+> EQLM = EQLM
ENUM s1 b1 <+> ENUM s2 b2                                = ENUM (s1 `union` s2) (b1 && b2)
SUPM t1    <+> SUPM t2 | equal 0 (Book M.empty []) t1 t2 = SUPM t1
_ <+> _ = NONE

extendName :: String -> String -> String
extendName nam@('$':_) suffix =        nam ++ "_" ++ suffix
extendName nam         suffix = "$" ++ nam ++ "_" ++ suffix

-- Main eta-reduction function
--
reduceEtas :: Int -> Term -> Term
reduceEtas d term = case term of
-- this assumes `t` is bound, because without this we can't (at least not easily) replace a var that is originally
-- an argument of a constructor in a match by a var of the newly-pulled-outward match of the reduction
  Lam k mty f ->
    case isEtaLong d k (f (Var k d)) of
      EMPM -> EmpM

      EQLM -> EqlM refl where
          nam = "$"++show d
          refl = reduceEtas d $ bindVarByName nam Rfl (resolveMatches d nam EQLM 0 "" [] (f (Var nam d)))

      UNIM -> UniM u where
          nam = "$"++show d
          u = reduceEtas d $ bindVarByName nam One (resolveMatches d nam UNIM 0 "" [] (f (Var nam d)))
                                                                                            -- if we don't use f (Var k d), 
                                                                                            -- then the recursive reduceEtas
                                                                                            -- won't know that it has found
                                                                                            -- a deeper app-lam-match on k
      BITM -> BitM fl tr where
          nam = "$"++show d
          fl = reduceEtas d $ bindVarByName nam Bt0 (resolveMatches d nam BITM 0 "" [] (f (Var nam d)))
          tr = reduceEtas d $ bindVarByName nam Bt1 (resolveMatches d nam BITM 1 "" [] (f (Var nam d)))

      NATM nams@[p] -> NatM z s where
          nam = "$"++show d
          z = reduceEtas d $ bindVarByName nam Zer (resolveMatches d nam (NATM [p]) 0 "" [] (f (Var nam d)))
          s = reduceEtas d (Lam p (Just Nat) (\q -> bindVarByName nam (Suc q) (resolveMatches (d+1) nam (NATM nams) 1 "" [Sub q] (f (Var nam d)))))

      LSTM nams@[h,t] -> LstM nil cons where
          nam = "$"++show d
          nil = reduceEtas d $ bindVarByName nam Nil (resolveMatches d nam (LSTM nams) 0 "" [] (f (Var nam d)))
          cons = reduceEtas d (Lam h Nothing (\h ->
                               Lam t Nothing (\t ->
                               bindVarByName nam (Con h t) (resolveMatches (d+2) nam (LSTM nams) 1 "" [Sub h, Sub t] (f (Var nam d))))))

      SIGM nams@[a,b] -> SigM pair where
          nam = "$"++show d
          pair = reduceEtas d (Lam a Nothing (\a ->
                               Lam b Nothing (\b ->
                               bindVarByName nam (Tup a b) (resolveMatches (d+2) nam (SIGM nams) 0 "" [Sub a, Sub b] (f (Var nam d))))))

      ENUM syms compl -> EnuM cases def where
        nam = "$"++show d
        cases = map (\sym -> (sym, reduceEtas d $ bindVarByName nam (Sym sym) (resolveMatches d nam (ENUM syms compl) 0 sym [] (f (Var nam d))))) syms
        def = if compl
            then reduceEtas d (Lam (extendName k "def") Nothing (\q -> bindVarByName nam q (resolveMatches (d+1) nam (ENUM syms compl) (-1) "" [Sub q] (f (Var nam d)))))
            else One
      
      -- SUPM lab -> SupM lab branches where
      --     branches = reduceEtas d (Lam (extendName k "0") Nothing (\l ->
      --                              Lam (extendName k "1") Nothing (\r ->
      --                              Let k Nothing l (\v ->
      --                              bindVarByName k v (resolveMatches (d+2) k (SUPM lab) 0 "" [Sub l, Sub r] (f (Var k d))))))
      --                             )

      -- NONE -> Lam k mty (\x -> reduceEtas d (f x))
      _ -> Lam k mty (\x -> reduceEtas (d+1) (f x))

  -- Not a Lam, just propagate deeper
  Var n i       -> Var n i
  Ref n i       -> Ref n i
  Sub t'        -> Sub t'
  Fix n f       -> Fix n (\v -> reduceEtas (d+1) (f v))
  Let n mty v f -> Let n (fmap (reduceEtas d) mty) (reduceEtas d v) (\v' -> reduceEtas (d+1) (f v'))
  Use n v f     -> Use n (reduceEtas d v) (\v' -> reduceEtas (d+1) (f v'))
  Set           -> Set
  Chk t' ty     -> Chk (reduceEtas d t') (reduceEtas d ty)
  Emp           -> Emp
  EmpM          -> EmpM
  Uni           -> Uni
  One           -> One
  UniM f        -> UniM (reduceEtas d f)
  Bit           -> Bit
  Bt0           -> Bt0
  Bt1           -> Bt1
  BitM f g      -> BitM (reduceEtas d f) (reduceEtas d g)
  Nat           -> Nat
  Zer           -> Zer
  Suc t'        -> Suc (reduceEtas d t')
  NatM z s      -> NatM (reduceEtas d z) (reduceEtas d s)
  Lst ty        -> Lst (reduceEtas d ty)
  Nil           -> Nil
  Con h t'      -> Con (reduceEtas d h) (reduceEtas d t')
  LstM nil c    -> LstM (reduceEtas d nil) (reduceEtas d c)
  Enu ss        -> Enu ss
  Sym s         -> Sym s
  EnuM cs def   -> EnuM [(s, reduceEtas d v) | (s,v) <- cs] (reduceEtas d def)
  Num nt        -> Num nt
  Val nv        -> Val nv
  Op2 o a b     -> Op2 o (reduceEtas d a) (reduceEtas d b)
  Op1 o a       -> Op1 o (reduceEtas d a)
  Sig a b       -> Sig (reduceEtas d a) (reduceEtas d b)
  Tup a b       -> Tup (reduceEtas d a) (reduceEtas d b)
  SigM f        -> SigM (reduceEtas d f)
  All a b       -> All (reduceEtas d a) (reduceEtas d b)
  App f x       -> App (reduceEtas d f) (reduceEtas d x)
  Eql ty a b    -> Eql (reduceEtas d ty) (reduceEtas d a) (reduceEtas d b)
  Rfl           -> Rfl
  EqlM f        -> EqlM (reduceEtas d f)
  Rwt e f       -> Rwt (reduceEtas d e) (reduceEtas d f)
  Met n ty args -> Met n (reduceEtas d ty) (map (reduceEtas d) args)
  Era           -> Era
  Sup l a b     -> Sup (reduceEtas d l) (reduceEtas d a) (reduceEtas d b)
  SupM l f      -> SupM (reduceEtas d l) (reduceEtas d f)
  Loc s t'      -> Loc s (reduceEtas d t')
  Log s x       -> Log (reduceEtas d s) (reduceEtas d x)
  Pri p         -> Pri p
  Pat ss ms cs  -> Pat (map (reduceEtas d) ss) [(k, reduceEtas d v) | (k,v) <- ms] [(map (reduceEtas d) ps, reduceEtas d rhs) | (ps,rhs) <- cs]
  Frk l a b     -> Frk (reduceEtas d l) (reduceEtas d a) (reduceEtas d b)
  Tst x         -> Tst (reduceEtas d x)

-- Updated resolveMatches that takes a list of arguments
resolveMatches :: Int -> Name -> ElimLabel -> Int -> String -> [Term] -> Term -> Term
resolveMatches d n l clause sym args t = case t of
  Lam k ty f   ->
    if k == n 
      then t 
      else Lam k (fmap (resolveMatches d n l clause sym args) ty) (\x -> resolveMatches (d+1) n l clause sym args (f x))
  App f x      ->
    case cut x of
      (Var k i) -> if k == n
        then case (cut f, l) of
          -- Unit matches
          (UniM u,     UNIM) -> resolveMatches d n l clause sym args u
          (UniM u,        _) -> UniM (resolveMatches d n l clause sym args u)

          -- Bit matches
          (BitM fl tr, BITM) -> 
            let branch = [fl, tr] !! clause
            in resolveMatches d n l clause sym args branch
          (BitM fl tr,    _) ->
            BitM (resolveMatches d n l clause sym args fl) (resolveMatches d n l clause sym args tr)

          -- Nat matches
          (NatM z s, NATM p) -> 
            case clause of
              0 -> resolveMatches d n l clause sym args z
              1 -> case (cut s, args) of
                     (Lam _ _ body, [q]) -> resolveMatches d n l clause sym args (body q)
                     _ -> foldl App (resolveMatches d n l clause sym args s) args
              _ -> error "Invalid clause for NatM"
          (NatM z s,    _) ->
            NatM (resolveMatches d n l clause sym args z) (resolveMatches d n l clause sym args s)

          -- Empty matches
          (EmpM, EMPM) -> resolveMatches d n l clause sym args EmpM  -- Empty match has no branches
          (EmpM, _)    -> EmpM
          
          -- List matches
          (LstM nil cons, LSTM nams) -> 
            case clause of
              0 -> resolveMatches d n l clause sym args nil
              1 -> case args of
                     [h, t] -> case cut cons of
                       Lam _ _ body1 -> case cut (body1 h) of
                         Lam _ _ body2 -> resolveMatches d n l clause sym args (body2 t)
                         _ -> error "LstM cons expects two lambda levels"
                       _ -> foldl App (resolveMatches d n l clause sym args cons) args
                     _ -> error "LstM cons case expects exactly two arguments"
              _ -> error "Invalid clause for LstM"
          (LstM nil cons, _) ->
            LstM (resolveMatches d n l clause sym args nil) (resolveMatches d n l clause sym args cons)
         
          -- Pair matches
          (SigM pair, SIGM nams) -> 
            case args of
              [a, b] -> case cut pair of
                Lam _ _ body1 -> case cut (body1 a) of
                  Lam _ _ body2 -> resolveMatches d n l clause sym args (body2 b)
                  _ -> error "SigM expects two lambda levels"
                _ -> foldl App (resolveMatches d n l clause sym args pair) args
              _ -> error "SigM expects exactly two arguments"
          (SigM pair, _) ->
            SigM (resolveMatches d n l clause sym args pair)         

          -- Sup matches
          (SupM label branches, SUPM lab) ->
            case args of
              [lft, rgt] -> case cut branches of
                Lam _ _ body1 -> case cut (body1 lft) of
                  Lam _ _ body2 -> resolveMatches d n l clause sym args (body2 rgt)
                  _             -> error "SupM expects two lambda levels"
                _             -> foldl App (resolveMatches d n l clause sym args branches) args
              _ -> error "SupM expects exactly two arguments"
          (SupM label branches, _) ->
            SupM (resolveMatches d n l clause sym args label) (resolveMatches d n l clause sym args branches)
          
          -- Equality matches
          (EqlM refl, EQLM) -> resolveMatches d n l clause sym args refl
          (EqlM refl, _)    -> EqlM (resolveMatches d n l clause sym args refl)

          -- Enum matches
          (EnuM cs def, ENUM syms _) ->
            if clause == -1 
              then
                case (cut def, args) of
                  (Lam _ _ body, [q]) -> resolveMatches (d+1) n l clause sym args (body q)
                  _                   -> def
              else 
                case lookup sym cs of
                  Just branch ->
                    resolveMatches d n l clause sym args branch
                  Nothing     ->
                    case cut def of
                      Lam defK mtdef defB -> resolveMatches (d+1) n l clause sym args (defB (Var k i))
                      _ -> error $ "Missing lambda in default case"
          (EnuM cs def, _) ->
            EnuM [(s, resolveMatches d n l clause sym args t) | (s,t) <- cs] (resolveMatches d n l clause sym args def)
          
          -- Not an eliminator application
          _ -> App (resolveMatches d n l clause sym args f) (resolveMatches d n l clause sym args x)
        else App (resolveMatches d n l clause sym args f) (resolveMatches d n l clause sym args x)
      _         -> App (resolveMatches d n l clause sym args f) (resolveMatches d n l clause sym args x)

  -- Not an eliminator application, just propagate deeper
  Var k i      -> Var k i
  Ref k i      -> Ref k i
  Sub t'       -> Sub (resolveMatches d n l clause sym args t')
  Fix k f      -> Fix k (\x -> resolveMatches (d+1) n l clause sym args (f x))
  Let k ty v f -> Let k (fmap (resolveMatches d n l clause sym args) ty) (resolveMatches d n l clause sym args v) (\x -> resolveMatches (d+1) n l clause sym args (f x))
  Use k v f    -> Use k (resolveMatches d n l clause sym args v) (\x -> resolveMatches (d+1) n l clause sym args (f x))
  Set          -> Set
  Chk t' ty    -> Chk (resolveMatches d n l clause sym args t') (resolveMatches d n l clause sym args ty)
  Emp          -> Emp
  EmpM         -> EmpM
  Uni          -> Uni
  One          -> One
  UniM f       -> UniM (resolveMatches d n l clause sym args f)
  Bit          -> Bit
  Bt0          -> Bt0
  Bt1          -> Bt1
  BitM f g     -> BitM (resolveMatches d n l clause sym args f) (resolveMatches d n l clause sym args g)
  Nat          -> Nat
  Zer          -> Zer
  Suc t'       -> Suc (resolveMatches d n l clause sym args t')
  NatM z s     -> NatM (resolveMatches d n l clause sym args z) (resolveMatches d n l clause sym args s)
  Lst ty       -> Lst (resolveMatches d n l clause sym args ty)
  Nil          -> Nil
  Con h t'     -> Con (resolveMatches d n l clause sym args h) (resolveMatches d n l clause sym args t')
  LstM nil c   -> LstM (resolveMatches d n l clause sym args nil) (resolveMatches d n l clause sym args c)
  Enu syms     -> Enu syms
  Sym s        -> Sym s
  EnuM cs def  -> EnuM (map (\(s,t') -> (s, resolveMatches d n l clause sym args t')) cs) (resolveMatches d n l clause sym args def)
  Num typ      -> Num typ
  Val v        -> Val v
  Op2 op a b   -> Op2 op (resolveMatches d n l clause sym args a) (resolveMatches d n l clause sym args b)
  Op1 op a     -> Op1 op (resolveMatches d n l clause sym args a)
  Sig a b      -> Sig (resolveMatches d n l clause sym args a) (resolveMatches d n l clause sym args b)
  Tup a b      -> Tup (resolveMatches d n l clause sym args a) (resolveMatches d n l clause sym args b)
  SigM f       -> SigM (resolveMatches d n l clause sym args f)
  All a b      -> All (resolveMatches d n l clause sym args a) (resolveMatches d n l clause sym args b)
  Eql ty a b   -> Eql (resolveMatches d n l clause sym args ty) (resolveMatches d n l clause sym args a) (resolveMatches d n l clause sym args b)
  Rfl          -> Rfl
  EqlM f       -> EqlM (resolveMatches d n l clause sym args f)
  Rwt e f      -> Rwt (resolveMatches d n l clause sym args e) (resolveMatches d n l clause sym args f)
  Met name ty as -> Met name (resolveMatches d n l clause sym args ty) (map (resolveMatches d n l clause sym args) as)
  Era          -> Era
  Sup l' a b   -> Sup (resolveMatches d n l clause sym args l') (resolveMatches d n l clause sym args a) (resolveMatches d n l clause sym args b)
  SupM l' f    -> SupM (resolveMatches d n l clause sym args l') (resolveMatches d n l clause sym args f)
  Loc span t'  -> Loc span (resolveMatches d n l clause sym args t')
  Log s x      -> Log (resolveMatches d n l clause sym args s) (resolveMatches d n l clause sym args x)
  Pri pf       -> Pri pf
  Pat ss ms cs -> Pat (map (resolveMatches d n l clause sym args) ss)
                      (map (\(m,t') -> (m, resolveMatches d n l clause sym args t')) ms)
                      (map (\(ps,rhs) -> (map (resolveMatches d n l clause sym args) ps, resolveMatches d n l clause sym args rhs)) cs)
  Frk l' a b   -> Frk (resolveMatches d n l clause sym args l') 
                      (resolveMatches d n l clause sym args a) 
                      (resolveMatches d n l clause sym args b)
  Tst x        -> Tst (resolveMatches d n l clause sym args x)

-- Check if a term contains the eta-long pattern: App (λ{...}) (Var name)
isEtaLong :: Int -> Name -> Term -> ElimLabel
isEtaLong d n t = case t of
  Lam k _ f   -> if k == n then NONE else isEtaLong (d+1) n (f (Var k d))
  App f x     ->
    case cut x of
      (Var k _) -> if k == n
        then
          case cut f of
          UniM _      -> UNIM <+> isEtaLong d n f
          BitM _ _    -> BITM <+> isEtaLong d n f
          NatM _ s    -> NATM (getVarName 1 s) <+> isEtaLong d n f
          EmpM        -> EMPM <+> isEtaLong d n f
          LstM _ c    -> LSTM (getVarName 2 c) <+> isEtaLong d n f
          SigM g      -> SIGM (getVarName 2 g) <+> isEtaLong d n f
          EqlM _      -> EQLM <+> isEtaLong d n f
          SupM l _    -> SUPM l <+> isEtaLong d n f
          EnuM cs def -> (ENUM (map fst cs) (isLam def)) <+> isEtaLong d n f
          _           -> isEtaLong d n f
        else
            isEtaLong d n f <+> isEtaLong d n x
      _ -> isEtaLong d n f <+> isEtaLong d n x
  Var _ _     -> NONE
  Ref _ _     -> NONE
  Sub t'      -> isEtaLong d n t'
  Fix k f     -> isEtaLong (d+1) n (f (Var k d))
  Let k t v f -> let def = isEtaLong d n v <+> isEtaLong (d+1) n (f (Var k d)) in fromMaybe def (fmap (\typ -> def <+> isEtaLong d n typ) t)
  Use k v f   -> isEtaLong d n v <+> isEtaLong (d+1) n (f (Var k d))
  Set         -> NONE
  Chk t' ty   -> isEtaLong d n t' <+> isEtaLong d n ty
  Emp         -> NONE
  EmpM        -> NONE
  Uni         -> NONE
  One         -> NONE
  UniM f      -> isEtaLong d n f
  Bit         -> NONE
  Bt0         -> NONE
  Bt1         -> NONE
  BitM f g    -> isEtaLong d n f <+> isEtaLong d n g
  Nat         -> NONE
  Zer         -> NONE
  Suc t'      -> isEtaLong d n t'
  NatM z s    -> isEtaLong d n z <+> isEtaLong d n s
  Lst ty      -> isEtaLong d n ty
  Nil         -> NONE
  Con h t'    -> isEtaLong d n h <+> isEtaLong d n t'
  LstM nil c  -> isEtaLong d n nil <+> isEtaLong d n c
  Enu _       -> NONE
  Sym _       -> NONE
  EnuM cs def -> foldr (<+>) (isEtaLong d n def) (map (isEtaLong d n . snd) cs)
  Num _       -> NONE
  Val _       -> NONE
  Op2 _ a b   -> isEtaLong d n a <+> isEtaLong d n b
  Op1 _ a     -> isEtaLong d n a
  Sig a b     -> isEtaLong d n a <+> isEtaLong d n b
  Tup a b     -> isEtaLong d n a <+> isEtaLong d n b
  SigM f      -> isEtaLong d n f
  All a b     -> isEtaLong d n a <+> isEtaLong d n b
  Eql ty a b  -> isEtaLong d n ty <+> isEtaLong d n a <+> isEtaLong d n b
  Rfl         -> NONE
  EqlM f      -> isEtaLong d n f
  Rwt e f     -> isEtaLong d n e <+> isEtaLong d n f
  Met _ ty cx -> isEtaLong d n ty <+> foldr (<+>) NONE (map (isEtaLong d n) cx)
  Era         -> NONE
  Sup l a b   -> isEtaLong d n l <+> isEtaLong d n a <+> isEtaLong d n b
  SupM l f    -> isEtaLong d n l <+> isEtaLong d n f
  Loc _ t'    -> isEtaLong d n t'
  Log s x     -> isEtaLong d n s <+> isEtaLong d n x
  Pri _       -> NONE
  Pat ss ms cs -> foldr (<+>) NONE (map (isEtaLong d n) ss ++ map (isEtaLong d n . snd) ms ++ concatMap (\(ps, rhs) -> map (isEtaLong d n) ps ++ [isEtaLong d n rhs]) cs)
  Frk l a b   -> isEtaLong d n l <+> isEtaLong d n a <+> isEtaLong d n b
  Tst x       -> isEtaLong d n x


getVarName 1 term = case cut term of
  Lam k _ _ -> [k]
  _ -> ["$noname"]
getVarName n term = case cut term of
  Lam k _ b -> k:(getVarName (n-1) (b (Var "_" 0)))
  _         -> ["$noname" | _ <- [1..n]]
