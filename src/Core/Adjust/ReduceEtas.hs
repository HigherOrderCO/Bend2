{-./Type.hs-}

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
              pair = reduceEtas d (Lam (k++"$l") Nothing (\a ->
                Lam (k++"$r") Nothing (\b ->
                  Use k (Tup a b) (\x -> (resolveMatches (d+2) k SIGM 0 [a, b] (f (Var k d)))))))

          SUPM -> SupM label branches where
              label = Var "label" d
              branches = reduceEtas d (Lam (k++"$l") Nothing (\l ->
                Lam (k++"$r") Nothing (\r ->
                  Use k (Sup label l r) (\x -> resolveMatches (d+2) k SUPM 0 [l, r] (f (Var k d))))))

          EQLM -> EqlM refl where
              refl = Use k Rfl (\x -> (reduceEtas d (resolveMatches d k EQLM 0 [] (f (Var k d)))))
          ENUM syms -> EnuM cases def where
            cases = [(sym, Use k (Sym sym) (\x -> 
                      reduceEtas d (resolveMatches d k (ENUM syms) i [] (f (Var k d)))))
                    | (i, sym) <- zip [0..] syms]
            def = reduceEtas d (Lam (k++"$def") Nothing (\y ->
                    Use k y (\x -> resolveMatches (d+1) k (ENUM syms) (-1) [] (f (Var k d)))))
            -- def = reduceEtas d (Use k (Var k d) (\x -> resolveMatches (d+1) k (ENUM syms) (-1) [] (f (Var k d))))

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

          -- (UniM u, UNIM) -> resolveMatches d n l clause args u
          (UniM u,     UNIM) -> resolveMatches d n l clause args u
          (UniM u,        _) -> UniM (resolveMatches d n l clause args u)

          -- (BitM fl tr, BITM) -> 
          --   let branch = [fl, tr] !! clause
          --   in resolveMatches d n l clause args branch
          (BitM fl tr, BITM) -> 
            let branch = [fl, tr] !! clause
            in resolveMatches d n l clause args branch
          (BitM fl tr,    _) -> BitM (resolveMatches d n l clause args fl) (resolveMatches d n l clause args tr)

          -- (NatM z s, NATM) -> 
          --   case clause of
          --     0 -> resolveMatches d n l clause args z
          --     1 -> foldl App (resolveMatches d n l clause args s) args
          --     _ -> error "Invalid clause for NatM"
          (NatM z s, NATM) -> 
            case clause of
              0 -> resolveMatches d n l clause args z
              1 -> -- Beta-reduce s with the predecessor argument
                   case (s, args) of
                     (Lam _ _ body, [q]) -> resolveMatches d n l clause args (body q)
                     _ -> foldl App (resolveMatches d n l clause args s) args
              _ -> error "Invalid clause for NatM"
          (NatM z s,    _) -> NatM (resolveMatches d n l clause args z) (resolveMatches d n l clause args s)

          -- (EmpM, EMPM) -> resolveMatches d n l clause args EmpM
          (EmpM, EMPM) -> resolveMatches d n l clause args EmpM  -- Empty match has no branches
          (EmpM, _) -> EmpM
          
          -- (LstM nil cons, LSTM) -> 
          --   case clause of
          --     0 -> resolveMatches d n l clause args nil
          --     1 -> foldl App (resolveMatches d n l clause args cons) args
          --     _ -> error "Invalid clause for LstM"
          (LstM nil cons, LSTM) -> 
            case clause of
              0 -> resolveMatches d n l clause args nil
              1 -> -- Beta-reduce cons with head and tail arguments
                   case args of
                     [h, t] -> case cons of
                       Lam _ _ body1 -> case body1 h of
                         Lam _ _ body2 -> resolveMatches d n l clause args (body2 t)
                         _ -> error "LstM cons expects two lambda levels"
                       _ -> foldl App (resolveMatches d n l clause args cons) args
                     _ -> error "LstM cons case expects exactly two arguments"
              _ -> error "Invalid clause for LstM"

          (LstM nil cons, _) -> LstM (resolveMatches d n l clause args nil) (resolveMatches d n l clause args cons)
         
          -- (SigM pair, SIGM) -> 
          --   -- foldl App (resolveMatches d n l clause args pair) args
          --   case args of
          --     [a, b] -> foldl App (resolveMatches d n l clause args pair) args
          --     _ -> error "SigM expects exactly two arguments"
          (SigM pair, SIGM) -> 
            -- Beta-reduce pair with both components
            case args of
              [a, b] -> case pair of
                Lam _ _ body1 -> case body1 a of
                  Lam _ _ body2 -> resolveMatches d n l clause args (body2 b)
                  _ -> error "SigM expects two lambda levels"
                _ -> foldl App (resolveMatches d n l clause args pair) args
              _ -> error "SigM expects exactly two arguments"
          (SigM pair, _) -> SigM (resolveMatches d n l clause args pair)         

          -- (SupM label branches, SUPM) ->
          --   foldl App (resolveMatches d n l clause args branches) args
          (SupM label branches, SUPM) ->
            -- Beta-reduce branches with left and right arguments
            case args of
              [lft, rgt] -> case branches of
                Lam _ _ body1 -> case body1 lft of
                  Lam _ _ body2 -> resolveMatches d n l clause args (body2 rgt)
                  _ -> error "SupM expects two lambda levels"
                _ -> foldl App (resolveMatches d n l clause args branches) args
              _ -> error "SupM expects exactly two arguments"
          (SupM label branches, _) -> SupM (resolveMatches d n l clause args label) (resolveMatches d n l clause args branches)
          
          -- (EqlM refl, EQLM) -> resolveMatches d n l clause args refl
          (EqlM refl, EQLM) -> resolveMatches d n l clause args refl
          (EqlM refl, _) -> EqlM (resolveMatches d n l clause args refl)

          -- (EnuM cs def, ENUM syms) ->
          --   if clause == -1 
          --     then resolveMatches d n l clause args def
          --     else 
          --       let sym = syms !! clause
          --       in case lookup sym cs of
          --         Just branch -> resolveMatches d n l clause args branch
          --         Nothing -> error $ "Missing case for symbol " ++ sym
          (EnuM cs def, ENUM syms) ->
            if clause == -1 
              then resolveMatches d n l clause args def  -- Default case
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
data ElimLabel
  = UNIM
  | BITM
  | NATM
  | EMPM  -- new
  | LSTM  -- new
  | SIGM  -- new
  | SUPM  -- new
  | EQLM  -- new
  | ENUM [String] -- new
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
  EnuM cs def -> foldr (<|>) (isEtaLong d n def) (map (isEtaLong d n . snd) cs) <|> isEtaLong d n def
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
      then case f of
        UniM _   -> Just UNIM
        BitM _ _ -> Just BITM
        NatM _ _ -> Just NATM
        EmpM     -> Just EMPM
        LstM _ _ -> Just LSTM
        SigM _   -> Just SIGM
        SupM _ _ -> Just SUPM
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
  -- _ -> trace "NOT" $ Nothing
