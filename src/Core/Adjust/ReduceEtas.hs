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
import Core.Show
import qualified Data.Set as S
import Debug.Trace
import Data.Maybe (isJust, fromJust)
import Control.Applicative

-- Main eta-reduction function
reduceEtas :: Int -> Term -> Term
reduceEtas d t = case t of
-- this assumes `t` is bound, because without this we can't (at least not easily) replace a var that is originally
-- an argument of a constructor in a match by a var of the newly-pulled-outward match of the reduction
  Var n i     -> Var n i
  Ref n i     -> Ref n i
  Sub t'      -> Sub (reduceEtas d t')
  Lam k mty f ->
    case isEtaLong d k (f (Var k d)) of
        Just lab -> case lab of
          UNIM -> UniM u where
              u = Use k One (\x -> (reduceEtas d (resolveMatches d k UNIM 0 [] (f (Var k d))))) -- if we don't use f (Var k d), 
                                                                                                -- then the recursive reduceEtas
                                                                                                -- won't know that it has found
                                                                                                -- a deeper app-lam-match on k

          BITM -> BitM fl tr where
              fl = Use k Bt0 (\x -> (reduceEtas d (resolveMatches d k BITM 0 [] (f (Var k d)))))
              tr = Use k Bt1 (\x -> (reduceEtas d (resolveMatches d k BITM 1 [] (f (Var k d)))))

          NATM -> NatM z s where
              z = Use k Zer (\x -> (reduceEtas d (resolveMatches d k NATM 0 [] (f (Var k d)))))
              s = reduceEtas d (Lam (k++"$p") Nothing (\q ->
                Use k (Suc q) (\x -> (resolveMatches (d+1) k NATM 1 [q] (f (Var k d))))))

          EMPM -> EmpM

          LSTM -> LstM nil cons where
              nil = Use k Nil (\x -> reduceEtas d (resolveMatches d k LSTM 0 [] (f (Var k d))))
              cons = reduceEtas d (Lam (k++"$h") Nothing (\h ->
                Lam (k++"$t") Nothing (\t ->
                  Use k (Con h t) (\x -> resolveMatches (d+2) k LSTM 1 [h, t] (f (Var k d))))))

          SIGM -> SigM pair where
              pair = reduceEtas d (Lam (k++"$a") Nothing (\a ->
                Lam (k++"$b") Nothing (\b ->
                  Use k (Tup a b) (\x -> (resolveMatches (d+2) k SIGM 0 [a, b] (f (Var k d)))))))

          SUPM lab -> SupM lab branches where
              branches = reduceEtas d (Lam (k++"$l") Nothing (\l ->
                Lam (k++"$r") Nothing (\r ->
                  Use k (Sup lab l r) (\x -> resolveMatches (d+2) k (SUPM lab) 0 [l, r] (f (Var k d))))))

          EQLM -> EqlM refl where
              refl = Use k Rfl (\x -> (reduceEtas d (resolveMatches d k EQLM 0 [] (f (Var k d)))))

          ENUM syms -> EnuM cases def where
            cases = [(sym, Use k (Sym sym) (\x -> 
                      reduceEtas d (resolveMatches d k (ENUM syms) i [] (f (Var k d)))))
                    | (i, sym) <- zip [0..] syms]
            def = reduceEtas d (Lam (k++"$def") Nothing (\q ->
              Use k q (\x -> (resolveMatches (d+1) k (ENUM syms) (-1) [q] (f (Var k d))))))

        Nothing -> Lam k mty (\x -> reduceEtas d (f x))
  Fix n f           -> Fix n (\v -> reduceEtas (d+1) (f v))
  Let n mty v f     -> Let n (fmap (reduceEtas d) mty) (reduceEtas d v) (\v' -> reduceEtas (d+1) (f v'))
  Use n v f         -> Use n (reduceEtas d v) (\v' -> reduceEtas (d+1) (f v'))
  Set -> Set
  Chk t' ty -> Chk (reduceEtas d t') (reduceEtas d ty)
  Emp  -> Emp
  EmpM -> EmpM
  Uni     -> Uni
  One     -> One
  UniM f  -> UniM (reduceEtas d f)
  Bit      -> Bit
  Bt0      -> Bt0
  Bt1      -> Bt1
  BitM f g -> BitM (reduceEtas d f) (reduceEtas d g)
  Nat      -> Nat
  Zer      -> Zer
  Suc t'   -> Suc (reduceEtas d t')
  NatM z s -> NatM (reduceEtas d z) (reduceEtas d s)
  Lst ty     -> Lst (reduceEtas d ty)
  Nil        -> Nil
  Con h t'   -> Con (reduceEtas d h) (reduceEtas d t')
  LstM nil c -> LstM (reduceEtas d nil) (reduceEtas d c)
  Enu ss      -> Enu ss
  Sym s       -> Sym s
  EnuM cs def -> EnuM [(s, reduceEtas d v) | (s,v) <- cs] (reduceEtas d def)
  Num nt    -> Num nt
  Val nv    -> Val nv
  Op2 o a b -> Op2 o (reduceEtas d a) (reduceEtas d b)
  Op1 o a   -> Op1 o (reduceEtas d a)
  Sig a b -> Sig (reduceEtas d a) (reduceEtas d b)
  Tup a b -> Tup (reduceEtas d a) (reduceEtas d b)
  SigM f  -> SigM (reduceEtas d f)
  All a b   -> All (reduceEtas d a) (reduceEtas d b)
  App f x   -> App (reduceEtas d f) (reduceEtas d x)
  Eql ty a b -> Eql (reduceEtas d ty) (reduceEtas d a) (reduceEtas d b)
  Rfl        -> Rfl
  EqlM f     -> EqlM (reduceEtas d f)
  Rwt e f    -> Rwt (reduceEtas d e) (reduceEtas d f)
  Met n ty args -> Met n (reduceEtas d ty) (map (reduceEtas d) args)
  Era       -> Era
  Sup l a b -> Sup (reduceEtas d l) (reduceEtas d a) (reduceEtas d b)
  SupM l f  -> SupM (reduceEtas d l) (reduceEtas d f)
  Loc s t' -> Loc s (reduceEtas d t')
  Log s x -> Log (reduceEtas d s) (reduceEtas d x)
  Pri p -> Pri p
  Pat ss ms cs -> Pat (map (reduceEtas d) ss) 
                      [(k, reduceEtas d v) | (k,v) <- ms]
                      [(map (reduceEtas d) ps, reduceEtas d rhs) | (ps,rhs) <- cs]
  Frk l a b    -> Frk (reduceEtas d l) (reduceEtas d a) (reduceEtas d b)
  Tst x -> Tst (reduceEtas d x)

-- Updated resolveMatches that takes a list of arguments
resolveMatches :: Int -> Name -> ElimLabel -> Int -> [Term] -> Term -> Term
resolveMatches d n l clause args t = case t of
  Var name i -> Var name i
  Ref name i -> Ref name i
  Sub t' -> Sub (resolveMatches d n l clause args t')
  
  Fix name f -> Fix name (\x -> resolveMatches (d+1) n l clause args (f x))
  Let name ty v f -> Let name (fmap (resolveMatches d n l clause args) ty) 
                       (resolveMatches d n l clause args v) 
                       (\x -> resolveMatches (d+1) n l clause args (f x))
  Use name v f -> Use name (resolveMatches d n l clause args v) 
                      (\x -> resolveMatches (d+1) n l clause args (f x))
  
  Set -> Set
  Chk t' ty -> Chk (resolveMatches d n l clause args t') (resolveMatches d n l clause args ty)
  Emp -> Emp
  EmpM -> EmpM
  Uni -> Uni
  One -> One
  UniM f -> UniM (resolveMatches d n l clause args f)
  Bit -> Bit
  Bt0 -> Bt0
  Bt1 -> Bt1
  BitM f g -> BitM (resolveMatches d n l clause args f) (resolveMatches d n l clause args g)
  Nat -> Nat
  Zer -> Zer
  Suc t' -> Suc (resolveMatches d n l clause args t')
  NatM z s -> NatM (resolveMatches d n l clause args z) (resolveMatches d n l clause args s)
  Lst ty -> Lst (resolveMatches d n l clause args ty)
  Nil -> Nil
  Con h t' -> Con (resolveMatches d n l clause args h) (resolveMatches d n l clause args t')
  LstM nil c -> LstM (resolveMatches d n l clause args nil) (resolveMatches d n l clause args c)
  Enu syms -> Enu syms
  Sym s -> Sym s
  EnuM cs def -> EnuM (map (\(s,t') -> (s, resolveMatches d n l clause args t')) cs) 
                      (resolveMatches d n l clause args def)
  Num typ -> Num typ
  Val v -> Val v
  Op2 op a b -> Op2 op (resolveMatches d n l clause args a) (resolveMatches d n l clause args b)
  Op1 op a -> Op1 op (resolveMatches d n l clause args a)
  Sig a b -> Sig (resolveMatches d n l clause args a) (resolveMatches d n l clause args b)
  Tup a b -> Tup (resolveMatches d n l clause args a) (resolveMatches d n l clause args b)
  SigM f -> SigM (resolveMatches d n l clause args f)
  All a b -> All (resolveMatches d n l clause args a) (resolveMatches d n l clause args b)
  Lam k ty f ->
    if k == n 
      then t 
      else Lam k (fmap (resolveMatches d n l clause args) ty) (\x -> resolveMatches (d+1) n l clause args (f x))
  App f x ->
    case cut x of
      (Var k i) -> if k == n
        then case (cut f, l) of

          (UniM u,     UNIM) -> resolveMatches d n l clause args u
          (UniM u,        _) -> UniM (resolveMatches d n l clause args u)

          (BitM fl tr, BITM) -> 
            let branch = [fl, tr] !! clause
            in resolveMatches d n l clause args branch
          (BitM fl tr,    _) -> BitM (resolveMatches d n l clause args fl) (resolveMatches d n l clause args tr)

          (NatM z s, NATM) -> 
            case clause of
              0 -> resolveMatches d n l clause args z
              1 -> -- Beta-reduce s with the predecessor argument
                   case (cut s, args) of
                     (Lam _ _ body, [q]) -> resolveMatches d n l clause args (body q)
                     _ -> foldl App (resolveMatches d n l clause args s) args
              _ -> error "Invalid clause for NatM"
          (NatM z s,    _) -> NatM (resolveMatches d n l clause args z) (resolveMatches d n l clause args s)

          (EmpM, EMPM) -> resolveMatches d n l clause args EmpM  -- Empty match has no branches
          (EmpM, _) -> EmpM
          
          (LstM nil cons, LSTM) -> 
            case clause of
              0 -> resolveMatches d n l clause args nil
              1 -> -- Beta-reduce cons with head and tail arguments
                   case args of
                     [h, t] -> case cut cons of
                       Lam _ _ body1 -> case cut (body1 h) of
                         Lam _ _ body2 -> resolveMatches d n l clause args (body2 t)
                         _ -> error "LstM cons expects two lambda levels"
                       _ -> foldl App (resolveMatches d n l clause args cons) args
                     _ -> error "LstM cons case expects exactly two arguments"
              _ -> error "Invalid clause for LstM"

          (LstM nil cons, _) -> LstM (resolveMatches d n l clause args nil) (resolveMatches d n l clause args cons)
         
          (SigM pair, SIGM) -> 
            -- Beta-reduce pair with both components
            case args of
              [a, b] -> case cut pair of
                Lam _ _ body1 -> case cut (body1 a) of
                  Lam _ _ body2 -> resolveMatches d n l clause args (body2 b)
                  _ -> error "SigM expects two lambda levels"
                _ -> foldl App (resolveMatches d n l clause args pair) args
              _ -> error "SigM expects exactly two arguments"
          (SigM pair, _) -> SigM (resolveMatches d n l clause args pair)         

          (SupM label branches, SUPM lab) ->
            -- Beta-reduce branches with left and right arguments
            case args of
              [lft, rgt] -> case cut branches of
                Lam _ _ body1 -> case cut (body1 lft) of
                  Lam _ _ body2 -> resolveMatches d n l clause args (body2 rgt)
                  _ -> error "SupM expects two lambda levels"
                _ -> foldl App (resolveMatches d n l clause args branches) args
              _ -> error "SupM expects exactly two arguments"
          (SupM label branches, _) -> SupM (resolveMatches d n l clause args label) (resolveMatches d n l clause args branches)
          
          -- (EqlM refl, EQLM) -> resolveMatches d n l clause args refl
          (EqlM refl, EQLM) -> resolveMatches d n l clause args refl
          (EqlM refl, _) -> EqlM (resolveMatches d n l clause args refl)

          (EnuM cs def, ENUM syms) ->
            if clause == -1 
              -- then resolveMatches d n l clause args def  -- Default case
              then case (cut def, args) of
                 (Lam _ _ body, [q]) -> resolveMatches d n l clause args (body q)
                 _ -> foldl App (resolveMatches d n l clause args def) args
              else 
                -- Get the symbol at this clause index
                let sym = syms !! clause
                in case lookup sym cs of
                  Just branch -> resolveMatches d n l clause args branch
                  Nothing -> error $ "Missing case for symbol " ++ sym
          (EnuM cs def, _) -> 
            EnuM [(s, resolveMatches d n l clause args t) | (s,t) <- cs]
                 (resolveMatches d n l clause args def)

          _      -> App (resolveMatches d n l clause args f) (resolveMatches d n l clause args x)
        else App (resolveMatches d n l clause args f) (resolveMatches d n l clause args x)
      _         -> App (resolveMatches d n l clause args f) (resolveMatches d n l clause args x)
  Eql ty a b -> Eql (resolveMatches d n l clause args ty) 
                    (resolveMatches d n l clause args a) 
                    (resolveMatches d n l clause args b)
  Rfl -> Rfl
  EqlM f -> EqlM (resolveMatches d n l clause args f)
  Rwt e f -> Rwt (resolveMatches d n l clause args e) (resolveMatches d n l clause args f)
  Met name ty as -> Met name (resolveMatches d n l clause args ty) 
                          (map (resolveMatches d n l clause args) as)
  Era -> Era
  Sup l' a b -> Sup (resolveMatches d n l clause args l') 
                    (resolveMatches d n l clause args a) 
                    (resolveMatches d n l clause args b)
  SupM l' f -> SupM (resolveMatches d n l clause args l') (resolveMatches d n l clause args f)
  Loc span t' -> Loc span (resolveMatches d n l clause args t')
  Log s x -> Log (resolveMatches d n l clause args s) (resolveMatches d n l clause args x)
  Pri pf -> Pri pf
  Pat ss ms cs -> Pat (map (resolveMatches d n l clause args) ss)
                     (map (\(m,t') -> (m, resolveMatches d n l clause args t')) ms)
                     (map (\(ps,rhs) -> (map (resolveMatches d n l clause args) ps, 
                                        resolveMatches d n l clause args rhs)) cs)
  Frk l' a b -> Frk (resolveMatches d n l clause args l') 
                    (resolveMatches d n l clause args a) 
                    (resolveMatches d n l clause args b)
  Tst x -> Tst (resolveMatches d n l clause args x)

data ElimLabel
  = UNIM
  | BITM
  | NATM
  | EMPM
  | LSTM
  | SIGM
  | SUPM Term
  | EQLM
  | ENUM [String]
  deriving Show

-- Check if a term contains the eta-long pattern: App (λ{...}) (Var name)
isEtaLong :: Int -> Name -> Term -> Maybe ElimLabel
isEtaLong d n t = case t of
  Var _ _ -> Nothing
  Ref _ _ -> Nothing
  Sub t' -> isEtaLong d n t'
  Fix k f -> isEtaLong (d+1) n (f (Var k d))
  Let k _ v f -> isEtaLong d n v <|> isEtaLong (d+1) n (f (Var k d))
  Use k v f -> isEtaLong d n v <|> isEtaLong (d+1) n (f (Var k d))
  Set -> Nothing
  Chk t' ty -> isEtaLong d n t' <|> isEtaLong d n ty
  Emp -> Nothing
  EmpM -> Nothing
  Uni -> Nothing
  One -> Nothing
  UniM f -> isEtaLong d n f
  Bit -> Nothing
  Bt0 -> Nothing
  Bt1 -> Nothing
  BitM f g -> isEtaLong d n f <|> isEtaLong d n g
  Nat -> Nothing
  Zer -> Nothing
  Suc t' -> isEtaLong d n t'
  NatM z s -> isEtaLong d n z <|> isEtaLong d n s
  Lst ty -> isEtaLong d n ty
  Nil -> Nothing
  Con h t' -> isEtaLong d n h <|> isEtaLong d n t'
  LstM nil c -> isEtaLong d n nil <|> isEtaLong d n c
  Enu _ -> Nothing
  Sym _ -> Nothing
  EnuM cs def -> foldr (<|>) (isEtaLong d n def) (map (isEtaLong d n . snd) cs)
  Num _ -> Nothing
  Val _ -> Nothing
  Op2 _ a b -> isEtaLong d n a <|> isEtaLong d n b
  Op1 _ a -> isEtaLong d n a
  Sig a b -> isEtaLong d n a <|> isEtaLong d n b
  Tup a b -> isEtaLong d n a <|> isEtaLong d n b
  SigM f -> isEtaLong d n f
  All a b -> isEtaLong d n a <|> isEtaLong d n b
  Lam k _ f -> if k == n then Nothing else isEtaLong (d+1) n (f (Var k d))
  App f x -> case cut x of
    (Var k _) -> if k == n
      then case cut f of
        UniM _   -> Just UNIM
        BitM _ _ -> Just BITM
        NatM _ _ -> Just NATM
        EmpM     -> Just EMPM
        LstM _ _ -> Just LSTM
        SigM _   -> Just SIGM
        SupM l _ -> Just (SUPM l)
        EqlM _   -> Just EQLM
        EnuM cs _ -> Just (ENUM (map fst cs))  -- Extract symbol order
        _      -> isEtaLong d n f
      else isEtaLong d n f <|> isEtaLong d n x
    _         -> isEtaLong d n f <|> isEtaLong d n x
  Eql ty a b -> isEtaLong d n ty <|> isEtaLong d n a <|> isEtaLong d n b
  Rfl -> Nothing
  EqlM f -> isEtaLong d n f
  Rwt e f -> isEtaLong d n e <|> isEtaLong d n f
  Met _ ty args -> isEtaLong d n ty <|> foldr (<|>) Nothing (map (isEtaLong d n) args)
  Era -> Nothing
  Sup l a b -> isEtaLong d n l <|> isEtaLong d n a <|> isEtaLong d n b
  SupM l f -> isEtaLong d n l <|> isEtaLong d n f
  Loc _ t' -> isEtaLong d n t'
  Log s x -> isEtaLong d n s <|> isEtaLong d n x
  Pri _ -> Nothing
  Pat ss ms cs -> foldr (<|>) Nothing (map (isEtaLong d n) ss ++ map (isEtaLong d n . snd) ms ++ concatMap (\(ps, rhs) -> map (isEtaLong d n) ps ++ [isEtaLong d n rhs]) cs)
  Frk l a b -> isEtaLong d n l <|> isEtaLong d n a <|> isEtaLong d n b
  Tst x -> isEtaLong d n x


-- -- Main eta-reduction function with lambda-inject optimization
-- reduceEtas :: Int -> Term -> Term
-- reduceEtas d t = case t of
--   -- Check for the lambda-inject pattern: λx. ... (λ{...} x)
--   Lam n ty f ->
--     case isEtaLong n d (f (Var n d)) of
--       Just (lmat, inj, hadTrust) ->
--         let t'  = injectInto inj n lmat in
--         let t'' = reduceEtas d t' in
--         -- If a top-level `trust` was encountered on the path to the match,
--         -- preserve it as an outer wrapper around the reduced case-tree.
--         if hadTrust then Tst t'' else t''
--       Nothing                    -> Lam n (fmap (reduceEtas d) ty) (\v -> reduceEtas (d+1) (f v))
--
--   -- Recursive cases for all other constructors
--   Var n i      -> Var n i
--   Ref n i      -> Ref n i
--   Sub t'       -> Sub (reduceEtas d t')
--   Fix n f      -> Fix n (\v -> reduceEtas (d+1) (f v))
--   Let k mt v f -> Let k (fmap (reduceEtas d) mt) (reduceEtas d v) (\v' -> reduceEtas (d+1) (f v'))
--   Use k v f    -> Use k (reduceEtas d v) (\v' -> reduceEtas (d+1) (f v'))
--   Set          -> Set
--   Chk a b      -> Chk (reduceEtas d a) (reduceEtas d b)
--   Tst a        -> Tst (reduceEtas d a)
--   Emp          -> Emp
--   EmpM         -> EmpM
--   Uni          -> Uni
--   One          -> One
--   UniM a       -> UniM (reduceEtas d a)
--   Bit          -> Bit
--   Bt0          -> Bt0
--   Bt1          -> Bt1
--   BitM a b     -> BitM (reduceEtas d a) (reduceEtas d b)
--   Nat          -> Nat
--   Zer          -> Zer
--   Suc n        -> Suc (reduceEtas d n)
--   NatM a b     -> NatM (reduceEtas d a) (reduceEtas d b)
--   Lst t'       -> Lst (reduceEtas d t')
--   Nil          -> Nil
--   Con h t'     -> Con (reduceEtas d h) (reduceEtas d t')
--   LstM a b     -> LstM (reduceEtas d a) (reduceEtas d b)
--   Enu ss       -> Enu ss
--   Sym s        -> Sym s
--   EnuM cs e    -> EnuM [(s, reduceEtas d v) | (s,v) <- cs] (reduceEtas d e)
--   Num nt       -> Num nt
--   Val nv       -> Val nv
--   Op2 o a b    -> Op2 o (reduceEtas d a) (reduceEtas d b)
--   Op1 o a      -> Op1 o (reduceEtas d a)
--   Sig a b      -> Sig (reduceEtas d a) (reduceEtas d b)
--   Tup a b      -> Tup (reduceEtas d a) (reduceEtas d b)
--   SigM a       -> SigM (reduceEtas d a)
--   All a b      -> All (reduceEtas d a) (reduceEtas d b)
--   App f x      -> App (reduceEtas d f) (reduceEtas d x)
--   Eql t' a b   -> Eql (reduceEtas d t') (reduceEtas d a) (reduceEtas d b)
--   Rfl          -> Rfl
--   EqlM f       -> EqlM (reduceEtas d f)
--   Met n t' cs  -> Met n (reduceEtas d t') (map (reduceEtas d) cs)
--   Era          -> Era
--   Sup l a b    -> Sup (reduceEtas d l) (reduceEtas d a) (reduceEtas d b)
--   SupM l f'    -> SupM (reduceEtas d l) (reduceEtas d f')
--   Loc s t'     -> Loc s (reduceEtas d t')
--   Log s x      -> Log (reduceEtas d s) (reduceEtas d x)
--   Pri p        -> Pri p
--   Pat ss ms cs -> Pat (map (reduceEtas d) ss) [(k, reduceEtas d v) | (k,v) <- ms] [(map (reduceEtas d) ps, reduceEtas d rhs) | (ps,rhs) <- cs]
--   Frk l a b    -> Frk (reduceEtas d l) (reduceEtas d a) (reduceEtas d b)
--   Rwt e f      -> Rwt (reduceEtas d e) (reduceEtas d f)
--
-- -- Check if a term matches the eta-long pattern: ... (λ{...} x)
-- -- Returns the lambda-match, an injection function, and whether a `trust`
-- -- marker was seen along the way (to be preserved outside after reduction).
-- isEtaLong :: Name -> Int -> Term -> Maybe (Term, Term -> Term, Bool)
-- isEtaLong target depth = go id depth False where
--   go :: (Term -> Term) -> Int -> Bool -> Term -> Maybe (Term, Term -> Term, Bool)
--   go inj d hadT term = case cut term of
--     -- Found intermediate lambda - add to injection
--     Lam n ty f -> 
--       go (\h -> inj (Lam n ty (\_ -> h))) (d+1) hadT (f (Var n d))
--
--     -- Found Let - add to injection
--     Let k mt v f ->
--       go (\h -> inj (Let k mt v (\_ -> h))) (d+1) hadT (f (Var k d))
--
--     -- Found Use - add to injection
--     Use k v f ->
--       go (\h -> inj (Use k v (\_ -> h))) (d+1) hadT (f (Var k d))
--
--     -- Found Chk - add to injection
--     Chk x t ->
--       go (\h -> inj (Chk h t)) d hadT x
--     -- Found Tst - record and continue, but don't push it inside branches
--     Tst x ->
--       go inj d True x
--
--     -- Found Loc - check if it wraps a lambda-match
--     Loc s x ->
--       if isLambdaMatch x
--         then go inj d hadT (Loc s x)  -- Don't inject Loc if it wraps a lambda-match
--         else go (\h -> inj (Loc s h)) d hadT x  -- Otherwise, add to injection
--
--     -- Found Log - add to injection
--     Log s x ->
--       go (\h -> inj (Log s h)) d hadT x
--
--     -- Pass through single-body lambda-matches (commuting conversion)
--     UniM b ->
--       case go id d hadT b of
--         Just (lmat, injB, tB) -> Just (lmat, \h -> inj (UniM (injB h)), tB)
--         Nothing           -> Nothing
--
--     SigM b ->
--       case go id d hadT b of
--         Just (lmat, injB, tB) -> Just (lmat, \h -> inj (SigM (injB h)), tB)
--         Nothing           -> Nothing
--
--     SupM l b ->
--       case go id d hadT b of
--         Just (lmat, injB, tB) -> Just (lmat, \h -> inj (SupM l (injB h)), tB)
--         Nothing           -> Nothing
--
--     EqlM b ->
--       case go id d hadT b of
--         Just (lmat, injB, tB) -> Just (lmat, \h -> inj (EqlM (injB h)), tB)
--         Nothing           -> Nothing
--
--     -- Conservative multi-arm pass-through: only if all arms agree on a common λ-match shape
--     BitM t f ->
--       case (go id d hadT t, go id d hadT f) of
--         (Just (l1, injT, tT), Just (l2, injF, tF))
--           | sameLambdaShape l1 l2 ->
--               Just (l1, \h -> inj (BitM (injT h) (injF h)), tT || tF)
--         _ -> Nothing
--
--     NatM z s ->
--       case (go id d hadT z, go id d hadT s) of
--         (Just (l1, injZ, tZ), Just (l2, injS, tS))
--           | sameLambdaShape l1 l2 ->
--               Just (l1, \h -> inj (NatM (injZ h) (injS h)), tZ || tS)
--         _ -> Nothing
--
--     LstM n c ->
--       case (go id d hadT n, go id d hadT c) of
--         (Just (l1, injN, tN), Just (l2, injC, tC))
--           | sameLambdaShape l1 l2 ->
--               Just (l1, \h -> inj (LstM (injN h) (injC h)), tN || tC)
--         _ -> Nothing
--
--     EnuM cs e ->
--       let rs = [(s, go id d hadT v) | (s,v) <- cs]
--           re = go id d hadT e
--       in
--       if all (isJust . snd) rs && isJust re then
--         let rcs       = [(s, fromJust m) | (s,m) <- rs]
--             (l0, _, _) = fromJust re
--             shapes = [lmShape l | (_, (l,_,_)) <- rcs] ++ [lmShape l0]
--         in case sequence shapes of
--              Just (sh0:rest) | all (== sh0) rest ->
--                let injCs          = [(s, injB) | (s, (_, injB, _)) <- rcs]
--                    (lmatE, injE, tE) = fromJust re
--                    tAny          = tE || or [t | (_, (_,_,t)) <- rcs]
--                in Just (lmatE, \h -> inj (EnuM [(s, injB h) | (s, injB) <- injCs] (injE h)), tAny)
--              _ -> Nothing
--       else Nothing
--
--     -- Found application - check if it's (λ{...} x) or if we can pass through
--     App f arg ->
--       case (f, cut f, cut arg) of
--         -- Check if f is a Loc-wrapped lambda-match and arg is our target variable
--         -- Keep the Loc wrapper on the lambda-match
--         (Loc s lmat, _, Var v_n _) | v_n == target && isLambdaMatch lmat ->
--           Just (Loc s lmat, inj, hadT)
--         -- Check if f is a lambda-match and arg is our target variable
--         (_, lmat, Var v_n _) | v_n == target && isLambdaMatch lmat ->
--           Just (lmat, inj, hadT)
--         -- Otherwise, pass through the application
--         _ -> go (\h -> inj (app h arg)) d hadT f
--
--     -- Any other form doesn't match our pattern
--     _ -> Nothing
--
-- -- FIXME: are the TODO cases below reachable? reason about it
--
-- -- Inject the injection function into each case of a lambda-match
-- injectInto :: (Term -> Term) -> Name -> Term -> Term
-- injectInto inj scrutName term = case term of
--   -- If the lambda-match is wrapped in Loc, preserve it
--   Loc s lmat -> Loc s (injectInto inj scrutName lmat)
--
--   -- Empty match - no cases to inject into
--   EmpM -> EmpM
--
--   -- Unit match - inject into the single case
--   UniM f -> UniM (injectBody [] inj scrutName (\_ -> One) f)
--
--   -- Bool match - inject into both cases
--   BitM f t -> BitM (injectBody [] inj scrutName (\_ -> Bt0) f) 
--                    (injectBody [] inj scrutName (\_ -> Bt1) t)
--
--   -- Nat match - special handling for successor case (1 field)
--   NatM z s -> NatM (injectBody [] inj scrutName (\_ -> Zer) z) 
--                    (injectBody ["p"] inj scrutName (\vars -> case vars of [p] -> Suc p; _ -> error $ "TODO: " ++ (show term)) s)
--
--   -- List match - special handling for cons case (2 fields)
--   LstM n c -> LstM (injectBody [] inj scrutName (\_ -> Nil) n) 
--                    (injectBody ["h", "t"] inj scrutName (\vars -> case vars of [h,t] -> Con h t; _ -> error $ "TODO: " ++ (show term)) c)
--
--   -- Enum match - inject into each case and default (apply default-case fix)
--   EnuM cs e -> EnuM [(s, injectBody [] inj scrutName (\_ -> Sym s) v) | (s,v) <- cs]
--                     (injectBody ["x"] inj scrutName (\vars -> case vars of [x] -> x; _ -> error $ "TODO: " ++ (show term)) e)
--
--   -- Sigma match - special handling for pair case (2 fields)
--   SigM f -> SigM (injectBody ["a", "b"] inj scrutName (\vars -> case vars of [a,b] -> Tup a b; _ -> error $ "TODO: " ++ (show term)) f)
--
--   -- Superposition match - special handling (2 fields)
--   SupM l f -> SupM l (injectBody ["a", "b"] inj scrutName (\vars -> case vars of [a,b] -> Sup l a b; _ -> error $ "TODO: " ++ (show term)) f)
--
--   -- Equality match - inject into the single case
--   EqlM f -> EqlM (injectBody [] inj scrutName (\_ -> Rfl) f)
--
--   -- Not a lambda-match
--   _ -> term
--
-- -- Helper to inject the injection function, skipping existing field lambdas
-- -- Also handles scrutinee reconstruction
-- injectBody :: [Name] -> (Term -> Term) -> Name -> ([Term] -> Term) -> Term -> Term
-- injectBody fields inj scrutName mkScrut body = go 0 fields [] [] body where
--   go :: Int -> [Name] -> [Term] -> [Name] -> Term -> Term
--   go d []     vars fieldNames body = 
--     let scrutVal = mkScrut (reverse vars)
--         -- Remove shadowed bindings from the injection
--         cleanedInj = removeShadowed fieldNames inj
--         -- Add scrutinee reconstruction if not shadowed
--         fullInj = if scrutName `notElem` fieldNames
--                   then \h -> Use scrutName scrutVal (\_ -> cleanedInj h)
--                   else cleanedInj
--     in fullInj body
--   go d (f:fs) vars fieldNames body = case cut body of
--     -- Existing field lambda - preserve it
--     Lam n ty b -> Lam n ty (\v -> go (d+1) fs (v:vars) (n:fieldNames) (b v))
--     -- Missing field lambda - add it
--     _          -> Lam f Nothing (\v -> go (d+1) fs (v:vars) (f:fieldNames) body)
--
-- -- Remove shadowed bindings from an injection function
-- removeShadowed :: [Name] -> (Term -> Term) -> (Term -> Term)
-- removeShadowed fieldNames inj = \body -> removeFromTerm fieldNames (inj body) where
--   removeFromTerm :: [Name] -> Term -> Term
--   removeFromTerm names term = case term of
--     -- Skip Use bindings that are shadowed
--     Use k v f | k `elem` names -> removeFromTerm names (f (Var k 0))
--     Use k v f                  -> Use k v (\x -> removeFromTerm names (f x))
--
--     -- Skip Let bindings that are shadowed
--     Let k mt v f | k `elem` names -> removeFromTerm names (f (Var k 0))
--     Let k mt v f                  -> Let k mt v (\x -> removeFromTerm names (f x))
--
--     -- For other constructs, just return as-is
--     _ -> term
--
-- -- Check if a term is a lambda-match (one of the match constructors)
-- isLambdaMatch :: Term -> Bool
-- isLambdaMatch term = case term of
--   EmpM     -> True
--   UniM _   -> True
--   BitM _ _ -> True
--   NatM _ _ -> True
--   LstM _ _ -> True
--   EnuM _ _ -> True
--   SigM _   -> True
--   SupM _ _ -> True
--   EqlM _   -> True
--   Loc _ t  -> isLambdaMatch t
--   _        -> False
--
-- -- Shapes of lambda-matches, used to conservatively commute multi-arm frames
-- data LmShape
--   = LM_Emp
--   | LM_Uni
--   | LM_Bit
--   | LM_Nat
--   | LM_Lst
--   | LM_Enu [String]
--   | LM_Sig
--   | LM_Sup
--   | LM_Eql
--   deriving (Eq, Show)
--
-- lmShape :: Term -> Maybe LmShape
-- lmShape t = case cut t of
--   EmpM       -> Just LM_Emp
--   UniM _     -> Just LM_Uni
--   BitM _ _   -> Just LM_Bit
--   NatM _ _   -> Just LM_Nat
--   LstM _ _   -> Just LM_Lst
--   EnuM cs _  -> Just (LM_Enu (map fst cs))
--   SigM _     -> Just LM_Sig
--   SupM _ _   -> Just LM_Sup
--   EqlM _     -> Just LM_Eql
--   Chk x _    -> lmShape x
--   Loc _ x    -> lmShape x
--   _          -> Nothing
--
-- sameLambdaShape :: Term -> Term -> Bool
-- sameLambdaShape a b = lmShape a == lmShape b
--
-- app :: Term -> Term -> Term
-- app (Lam k _ f) x = Use k x f
-- app f           x = App f x
