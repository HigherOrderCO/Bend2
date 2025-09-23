{-./Type.hs-}
{-./Show.hs-}

-- Bidirectional Type Checker with Application Splitting
-- ======================================================
--
-- This module implements a bidirectional type checker that:
-- 1) Checks terms against expected types (check mode)
-- 2) Infers types from term structure (infer mode)  
-- 3) Splits certain eliminator applications into applications of auxiliary definitions
--
-- Key Functions:
-- -------------
-- check        -> verifies term has expected type, may transform the term
-- infer        -> synthesizes type from term, either from its structure or from how it's used
--   inferStructural -> infers the type of a term by looking at its structure
--   inferIndirect   -> infers the type of a term by looking at how it's used in an "environment" term
-- verify       -> helper that infers then compares with expected type
--
-- Application Splitting:
-- ---------------------
-- When checking applications of eliminators like (App (NatM z s) x) : T, 
-- the checker introduces auxiliary definitions:
--   let $aux_n : ∀x:Nat. T = 
--     (NatM z s) 
--   in $aux_n(x)
--
-- Indirect Inference:
-- ------------------
-- For terms like λx. body where x's type is unknown, inferIndirect
-- analyzes how x is used in body to reconstruct its type.
-- Example: from λx. True or x, infers x : Bool
{-# LANGUAGE ViewPatterns #-}

module Core.BigCheck where

import Control.Monad (unless)
import Control.Monad (unless, foldM)
import Data.List (find)
import Data.Maybe (fromJust, fromMaybe, listToMaybe)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

import Core.Bind
import Core.Type
import Core.Show
import Core.Equal
import Core.Rewrite
import Core.WHNF
import Core.Adjust.ReduceEtas

-- Utils
-- -------

extend :: Ctx -> Name -> Term -> Term -> Ctx
extend (Ctx ctx) k v t = Ctx (ctx ++ [(k, v, t)])

reWrap :: Term -> Term -> Term
reWrap (Loc l _) z = Loc l z
reWrap (Chk x t) z = Chk z t
reWrap _        z = z

-- Type Checker
-- ------------
--
-- Indirect type inference by usage analysis
-- 1) Traverses term looking for uses of variable 'var'
-- 2) Reconstructs var's type based on how it's used
-- 3) Returns "_unconstrained" for ambiguous cases
-- 4) Handles special case of dependent pairs (Tup a b)
--
-- Strategy: if var appears as argument to f : A -> B, then infer var : A
inferIndirect :: Int -> Span -> Book -> Ctx -> Term -> Term -> Result Term
inferIndirect d span book ctx target term = 
  do
  let def = findDefault target term
  result <- inferIndirectGo d span book ctx target term
  comp   <- replaceUnconstrained d span book ctx result target def
  return comp
  where
    findDefault :: Term -> Term -> Maybe Term
    findDefault (cut -> Tup a b) term = case infer d span book ctx b Nothing of
      Done bT -> Just bT
      _       -> Nothing
    findDefault x term = Nothing

replaceUnconstrained :: Int -> Span -> Book -> Ctx -> Term -> Term -> Maybe Term -> Result Term
replaceUnconstrained d span book ctx term target def = do
  case def of
    Just def -> return $ rewrite d book (Var "_unconstrained" 0) def term
    Nothing  -> Fail $ CantInfer (getSpan span target) (normalCtx book ctx) Nothing

-- Core indirect inference traversal
-- 1) At each term constructor, analyzes if/how 'var' appears
-- 2) For compound terms, recursively infers from subterms
-- 3) Uses unifyTerms to combine constraints from multiple uses
-- 4) Special handling for lambda-bound variables (stops if var is shadowed)
--
-- Returns: inferred type for 'var', or "_unconstrained" if no constraint on the type of 'var' was found
inferIndirectGo :: Int -> Span -> Book -> Ctx -> Term -> Term -> Result Term
inferIndirectGo d span book ctx var@(cut -> Tup a b) term@(cut -> App (cut -> SigM g) x) = 
  do
  if eql False d book var x
  then do
      aT <- infer d span book ctx a Nothing
      let bT = infer d span book ctx b Nothing
      case bT of
        Done bT@(cut ->App bTFunc a') | eql False d book a a' -> return $ Sig aT bTFunc
        r -> do
          case cut g of
            Lam l mtl lb -> do
              case cut (lb (Var l d)) of
                Lam r mtr rb -> do
                  rT <- inferIndirectGo d span book (extend ctx l (Var l d) aT) (Var r (d+1)) (rb (Var r (d+1)))
                  return $ Sig aT (Lam l (Just aT) (\v -> bindVarByName l v rT))
                _ -> do
                  Fail $ CantInfer (getSpan span x) (normalCtx book ctx) Nothing
            _ -> do
              res <- do
                let new_var = Var "$b" d
                let new_term = appInnerArg 1 g new_var
                bTFunc <-
                  do
                  bTFunc' <- inferIndirectGo (d+1) span book (extend ctx "$b" new_var (Var "_unconstrained" 0)) new_var new_term
                  case r of
                    Done bT -> replaceUnconstrained d span book ctx bTFunc' b (Just bT)
                    _       -> return bTFunc'
                return $ Sig aT bTFunc
              return res
  else Fail $ CantInfer (getSpan span x) (normalCtx book ctx) Nothing
  where 
    appInnerArg 0 func arg = App func arg
    appInnerArg l func arg = case cut func of
      Lam k mt b  -> Lam k mt (\x -> appInnerArg (l-1) (b x) arg) 
      EmpM        -> EmpM
      EqlM f      -> EqlM (appInnerArg (l-1) f arg)
      UniM f      -> UniM (appInnerArg (l-1) f arg) 
      BitM f t    -> BitM (appInnerArg (l-1) f arg) (appInnerArg (l-1) t arg)
      LstM h t    -> LstM (appInnerArg (l-1) h arg) (appInnerArg (l-1) t arg)
      NatM z s    -> NatM (appInnerArg (l-1) z arg) (appInnerArg (l) s arg)
      SigM g      -> SigM (appInnerArg (l-1) g arg)
      EnuM cs def -> EnuM (map (\(s,t) -> (s, appInnerArg (l-1) t arg)) cs) (appInnerArg (l-1) def arg)
      _ -> error "unreachaboe appInnerArg"

inferIndirectGo d span book ctx target@(cut -> SigM g) term@(cut -> App (cut -> SigM g') x@(cut -> Var k i)) = 
  do
  if eql False d book g g'
  then do
    xT <- infer d span book ctx x Nothing
    case cut xT of
      Sig lT rTFunc -> do
        case cut g of
          Lam l mtl lb -> do
            case cut (lb (Var l d)) of
              Lam r mtr rb -> do
                let rT = App rTFunc (Var l d) 
                gT <- infer d span book (extend (extend ctx l (Var l d) lT) r (Var r (d+1)) rT) (rb (Var r (d+1))) Nothing
                return $ All (Sig lT (Lam l (Just lT) (\v -> bindVarByName l v rT))) (Lam l mtl (\lv -> Lam r mtr (\rv -> bindVarByNameMany [(l,lv),(r,rv)] gT)))
              _ -> do
                Fail $ CantInfer (getSpan span x) (normalCtx book ctx) Nothing
          _ -> do
            Fail $ CantInfer (getSpan span x) (normalCtx book ctx) Nothing
      _ -> Fail $ CantInfer span (normalCtx book ctx) Nothing
  else Fail $ CantInfer (getSpan span x) (normalCtx book ctx) Nothing

inferIndirectGo d span book ctx var@(Var k i) term = do
  case term of
    Var x j -> do
      return (Var "_unconstrained" 0)

    Chk x t | eql False d book x var -> do
      return t
    Chk x t -> do
      t1 <- inferIndirectGo d span book ctx var x
      t2 <- inferIndirectGo d span book ctx var t
      unifyOrFail t1 t2

    Loc _ t -> do
      inferIndirectGo d span book ctx var t
    
    Tst x -> do
      inferIndirectGo d span book ctx var x

    Lam x mt b | x == k -> do
      return (Var "_unconstrained" 0)
    Lam x mt b -> do
      case mt of
        Just t -> do
          bType <- inferIndirectGo (d+1) span book (extend ctx x (Var x d) t) var (b (Var x d))
          return $ Lam x mt (\v -> bindVarByName x v bType)
        Nothing -> do
          Fail $ CantInfer span (normalCtx book ctx) Nothing

    NatM z s -> do
      t1 <- inferIndirectGo d span book ctx var z
      t2 <- inferIndirectGo d span book ctx var s
      return $ NatM t1 t2

    App f x | eql False d book x var -> do
      case infer d (getSpan span f) book ctx f Nothing of
        Done fT -> do
          case cut fT of
            All xT _ -> return xT
            _        -> inferIndirectGo d span book ctx var f
        _ -> case cut f of
          Lam _ Nothing b -> inferIndirectGo d span book ctx var (b x)
          _               -> inferIndirectGo d span book ctx var f
    App f x | not $ eql False d book f var -> do
      case cut f of
        SigM g -> do
          fT <- inferIndirect d span book ctx f (App f x)
          t1 <- case cut fT of
            All aT bT -> case cut g of
              Lam a mta ba -> case cut (ba (Var a d)) of
                Lam b mtb bb -> do
                  inferIndirect (d+2) span book (extend (extend ctx a (Var a d) aT) b (Var b (d+1)) (App bT (Var a d))) var (bb (Var b (d+1)))
                _ -> Fail $ CantInfer span (normalCtx book ctx) Nothing
              _ -> Fail $ CantInfer span (normalCtx book ctx) Nothing
            _ -> Fail $ CantInfer span (normalCtx book ctx) Nothing
          t2 <- inferIndirectGo d span book ctx var x
          return t1
        _ -> do
          t1 <- inferIndirectGo d span book ctx var f
          t2 <- inferIndirectGo d span book ctx var x
          if equal d book t1 (Var "_unconstrained" 0)
          then return t2
          else unifyOrFail (App t1 x) t2
    App f x -> do
      t1 <- inferIndirectGo d span book ctx var f
      t2 <- inferIndirectGo d span book ctx var x
      unifyOrFail t1 t2

    Suc p | eql False d book p var -> do
      return $ Nat
    Suc p  -> do
      inferIndirectGo d span book ctx var p

    Con h t | eql False d book h var -> do
      tT <- infer d (getSpan span t) book ctx t Nothing
      case cut tT of
        Lst hT -> return $ (Lst hT)
        _      -> return (Var "_unconstrained" 0)
    Con h t | eql False d book t var -> do
      hT <- infer d (getSpan span h) book ctx h Nothing
      return $ (Lst hT)
    Con h t -> do
      t1 <- inferIndirectGo d span book ctx var h
      t2 <- inferIndirectGo d span book ctx var t
      unifyOrFail t1 t2

    Ref k j -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    Sub x -> do
      inferIndirectGo d span book ctx var x

    Fix k f -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    Let k t v f -> do
      case t of
        Just t | eql False d book var t -> do
          return Set
        Just t -> do
          t1 <- inferIndirectGo d span book ctx var t
          t2 <- inferIndirectGo d span book ctx var v
          t3 <- inferIndirectGo (d+1) span book (extend ctx k v t) var (f (Var k d))
          t4 <- unifyOrFail t1 t2
          unifyOrFail t3 t4
        _ -> do
          case infer d span book ctx v Nothing of
            Done t -> do
              t1 <- inferIndirectGo d span book ctx var t
              t2 <- inferIndirectGo d span book ctx var v
              t3 <- inferIndirectGo (d+1) span book (extend ctx k v t) var (f (Var k d))
              t4 <- unifyOrFail t1 t2
              unifyOrFail t3 t4
            _ -> do
              inferIndirectGo d span book ctx var v

    Use k v f -> do
      inferIndirectGo d span book ctx var (f v)

    Set -> do
      return (Var "_unconstrained" 0)

    Emp -> do
      return (Var "_unconstrained" 0)

    EmpM -> do
      return (Var "_unconstrained" 0)

    Uni -> do
      return (Var "_unconstrained" 0)

    One -> do
      return (Var "_unconstrained" 0)

    UniM f -> do
      t <- inferIndirectGo d span book ctx var f
      return $ UniM t

    Bit -> do
      return (Var "_unconstrained" 0)

    Bt0 -> do
      return (Var "_unconstrained" 0)

    Bt1 -> do
      return (Var "_unconstrained" 0)

    BitM f t -> do
      t1 <- inferIndirectGo d span book ctx var f
      t2 <- inferIndirectGo d span book ctx var t
      return $ BitM t1 t2

    Nat -> do
      return (Var "_unconstrained" 0)

    Zer -> do
      return (Var "_unconstrained" 0)

    Lst t | eql False d book var t -> do
      return Set
    Lst t  -> do
      inferIndirectGo d span book ctx var t

    Nil -> do
      return (Var "_unconstrained" 0)

    LstM n c -> do
      t1 <- inferIndirectGo d span book ctx var n
      t2 <- inferIndirectGo d span book ctx var c
      return $ LstM t1 t2

    Enu syms -> do
      return (Var "_unconstrained" 0)

    Sym s -> do
      return (Var "_unconstrained" 0)

    EnuM cs@((s,t):_) df -> do
      domainT <- infer d span book ctx (Sym s) Nothing
      defau   <- case cut df of
            Lam def mtd bd -> inferIndirectGo (d+1) span book (extend ctx def (Var def d) domainT) var (bd (Var def d))
            _              -> Fail $ CantInfer span (normalCtx book ctx) Nothing
      ts <- mapM (\(s, t) -> inferIndirectGo d span book ctx var t) cs
      return $ EnuM [(s, t) | (s, _) <- cs, t <- ts] defau
    EnuM _ _ -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    Num t -> do
      return (Var "_unconstrained" 0)

    Val v -> do
      return (Var "_unconstrained" 0)

    Op2 op a b | eql False d book var a || eql False d book var b -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing
    Op2 op a b -> do
      t1 <- inferIndirectGo d span book ctx var a
      t2 <- inferIndirectGo d span book ctx var b
      unifyOrFail t1 t2

    Op1 op a | eql False d book var a -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing
    Op1 op a -> do
      inferIndirectGo d span book ctx var a

    Sig a b | eql False d book var a && not (eql False d book var b) -> do
      t2 <- inferIndirectGo d span book ctx var b
      unifyOrFail Set t2
    Sig a b | not (eql False d book var a) && not (eql False d book var b) -> do
      t1 <- inferIndirectGo d span book ctx var a
      t2 <- inferIndirectGo d span book ctx var b
      unifyOrFail t1 t2
    Sig a b -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    Tup a b | not (eql False d book var a || eql False d book var b) -> do
      t1 <- inferIndirectGo d span book ctx var a
      t2 <- inferIndirectGo d span book ctx var b
      unifyOrFail t1 t2
    Tup a b -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    SigM f -> do
      t1 <- inferIndirectGo d span book ctx var f
      return $ SigM t1

    All a b | eql False d book var a && not (eql False d book var b) -> do
      t2 <- inferIndirectGo d span book ctx var b
      unifyOrFail Set t2
    All a b | not (eql False d book var b) -> do
      t1 <- inferIndirectGo d span book ctx var a
      t2 <- inferIndirectGo d span book ctx var b
      unifyOrFail t1 t2
    All a b -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    Eql t a b | eql False d book var a -> do
      t1 <- inferIndirectGo d span book ctx var a
      t2 <- inferIndirectGo d span book ctx var b
      t3 <- unifyOrFail t1 t2
      unifyOrFail Set t3
    Eql t a b -> do
      t1 <- inferIndirectGo d span book ctx var a
      t2 <- inferIndirectGo d span book ctx var b
      t3 <- inferIndirectGo d span book ctx var t
      t4 <- unifyOrFail t1 t2
      unifyOrFail t3 t4

    Rfl -> do
      return (Var "_unconstrained" 0)

    EqlM f -> do
      t1 <- inferIndirectGo d span book ctx var f
      return $ EqlM t1

    Rwt e f -> do
      t1 <- inferIndirectGo d span book ctx var e  
      t2 <- inferIndirectGo d span book ctx var f
      unifyOrFail t1 t2

    Met n t xs -> do
      t1 <- inferIndirectGo d span book ctx var t
      ts <- mapM (inferIndirectGo d span book ctx var) xs
      foldM unifyOrFail t1 ts

    Era -> do
      return (Var "_unconstrained" 0)

    Sup l a b | eql False d book var l -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing
    Sup l a b -> do
      t1 <- inferIndirectGo d span book ctx var a
      t2 <- inferIndirectGo d span book ctx var b
      unifyOrFail t1 t2

    SupM l f | eql False d book var l -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing
    SupM l f -> do
      t1 <- inferIndirectGo d span book ctx var l
      t2 <- inferIndirectGo d span book ctx var f
      unifyOrFail t1 t2

    Log s x | eql False d book var s -> do
      t1 <- inferIndirectGo d span book ctx var x
      unifyOrFail (Lst (Num CHR_T)) t1
    Log s x -> do
      t1 <- inferIndirectGo d span book ctx var s
      t2 <- inferIndirectGo d span book ctx var x
      unifyOrFail t1 t2

    Pri p -> do
      return (Var "_unconstrained" 0)

    Pat ps ms cs -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    Frk l a b | eql False d book var l -> do
      t1 <- inferIndirectGo d span book ctx var a
      t2 <- inferIndirectGo d span book ctx var b
      t3 <- unifyOrFail t1 t2
      unifyOrFail (Num U64_T) t3
    Frk l a b -> do
      t1 <- inferIndirectGo d span book ctx var a
      t2 <- inferIndirectGo d span book ctx var b
      t3 <- inferIndirectGo d span book ctx var l
      t4 <- unifyOrFail t1 t2
      unifyOrFail t3 t4

  where
    unifyOrFail t1 t2 = case unifyTerms d book t1 t2 of
      Just t -> return t
      Nothing -> Fail $ CantInfer span (normalCtx book ctx) Nothing

inferIndirectGo d span book ctx target term = 
  Fail $ CantInfer span (normalCtx book ctx) Nothing

-- Unifies two type terms, preferring constrained over unconstrained
-- 1) "_unconstrained" acts as wildcard, unified with anything
-- 2) For structured types, unifies recursively 
-- 3) For incompatible types, returns Nothing
-- 4) Preserves location information (Loc nodes)
--
-- Returns: Just unified_type, or Nothing if unification fails
unifyTerms :: Int -> Book -> Term -> Term -> Maybe Term
unifyTerms d book t1 t2 = case (t1, t2) of
  -- If one is a variable (unconstrained), take the other
  (Var "_unconstrained" _, t) -> Just t
  (t, Var "_unconstrained" _) -> Just t

  -- For structured terms, unify recursively
  (BitM f1 t1, BitM f2 t2) -> do
    f' <- unifyTerms d book f1 f2
    t' <- unifyTerms d book t1 t2
    return $ BitM f' t'

  (NatM z1 s1, NatM z2 s2) -> do
    z' <- unifyTerms d book z1 z2
    s' <- unifyTerms d book s1 s2
    return $ NatM z' s'

  (App f1 x1, App f2 x2) -> do
    f' <- unifyTerms d book f1 f2
    x' <- unifyTerms d book x1 x2
    return $ App f' x'

  (Lam k1 mt1 b1, Lam k2 mt2 b2) | k1 == k2 -> do
    mt' <- case (mt1, mt2) of
      (Just t1, Just t2) -> Just <$> unifyTerms d book t1 t2
      (Just t, Nothing) -> return $ Just t
      (Nothing, Just t) -> return $ Just t
      (Nothing, Nothing) -> return Nothing
    bt <- unifyTerms (d+1) book (b1 (Var k1 d)) (b2 (Var k1 d))
    return $ Lam k1 mt' (\v -> bindVarByIndex d v bt)

  (Chk v1 t1, Chk v2 t2) -> do
    v' <- unifyTerms d book v1 v2
    t' <- unifyTerms d book t1 t2
    return $ Chk v' t'

  (Let k1 mt1 v1 f1, Let k2 mt2 v2 f2) | k1 == k2 -> do
    mt' <- case (mt1, mt2) of
      (Just t1, Just t2) -> Just <$> unifyTerms d book t1 t2
      (Just t, Nothing) -> return $ Just t
      (Nothing, Just t) -> return $ Just t
      (Nothing, Nothing) -> return Nothing
    v' <- unifyTerms d book v1 v2
    let unique_dummy = Var "__" (-1)
    b' <- unifyTerms (d+1) book (f1 unique_dummy) (f2 unique_dummy)
    return $ Let k1 mt' v' (\x -> bindVarByIndex (-1) x b')

  (Use k1 v1 f1, Use k2 v2 f2) | k1 == k2 -> do
    let unique_dummy = Var "__" (-1)
    v' <- unifyTerms d book v1 v2
    f' <- unifyTerms d book (f1 unique_dummy) (f2 unique_dummy)
    return $ Use k1 v' (\x -> bindVarByIndex (-1) x f')

  (Fix k1 f1, Fix k2 f2) | k1 == k2 -> do
    let unique_dummy = Var "__" (-1)
    b' <- unifyTerms d book (f1 unique_dummy) (f2 unique_dummy)
    return $ Fix k1 (\x -> bindVarByIndex (-1) x b')

  (Loc l1 t1, Loc l2 t2) -> do
    t' <- unifyTerms d book t1 t2
    return $ Loc l1 t'

  (Loc l t1, t2) -> do
   t <- unifyTerms d book t1 t2
   return $ Loc l t
  (t1, Loc l t2) -> do
   t <- unifyTerms d book t1 t2
   return $ Loc l t

  (Sub x1, Sub x2) -> do
    x' <- unifyTerms d book x1 x2
    return $ Sub x'

  (UniM f1, UniM f2) -> do
    f' <- unifyTerms d book f1 f2
    return $ UniM f'

  (Suc n1, Suc n2) -> do
    n' <- unifyTerms d book n1 n2
    return $ Suc n'

  (Lst t1, Lst t2) -> do
    t' <- unifyTerms d book t1 t2
    return $ Lst t'

  (Con h1 t1, Con h2 t2) -> do
    h' <- unifyTerms d book h1 h2
    t' <- unifyTerms d book t1 t2
    return $ Con h' t'

  (LstM n1 c1, LstM n2 c2) -> do
    n' <- unifyTerms d book n1 n2
    c' <- unifyTerms d book c1 c2
    return $ LstM n' c'

  (EnuM cs1 df1, EnuM cs2 df2) | map fst cs1 == map fst cs2 -> do
      cs' <- sequence [ (,) s <$> unifyTerms d book t1 t2 
                      | ((s,t1), (_,t2)) <- zip cs1 cs2 ]
      df' <- unifyTerms d book df1 df2
      return $ EnuM cs' df'

  (Op2 op1 a1 b1, Op2 op2 a2 b2) | op1 == op2 -> do
    a' <- unifyTerms d book a1 a2
    b' <- unifyTerms d book b1 b2
    return $ Op2 op1 a' b'

  (Op1 op1 a1, Op1 op2 a2) | op1 == op2 -> do
    a' <- unifyTerms d book a1 a2
    return $ Op1 op1 a'

  (Sig a1 b1, Sig a2 b2) -> do
    a' <- unifyTerms d book a1 a2
    b' <- unifyTerms d book b1 b2
    return $ Sig a' b'

  (Tup a1 b1, Tup a2 b2) -> do
    a' <- unifyTerms d book a1 a2
    b' <- unifyTerms d book b1 b2
    return $ Tup a' b'

  (SigM f1, SigM f2) -> do
    f' <- unifyTerms d book f1 f2
    return $ SigM f'

  (All a1 b1, All a2 b2) -> do
    a' <- unifyTerms d book a1 a2
    b' <- unifyTerms d book b1 b2
    return $ All a' b'

  (Eql t1 a1 b1, Eql t2 a2 b2) -> do
    t' <- unifyTerms d book t1 t2
    a' <- unifyTerms d book a1 a2
    b' <- unifyTerms d book b1 b2
    return $ Eql t' a' b'

  (EqlM f1, EqlM f2) -> do
    f' <- unifyTerms d book f1 f2
    return $ EqlM f'

  (Rwt e1 f1, Rwt e2 f2) -> do
    e' <- unifyTerms d book e1 e2
    f' <- unifyTerms d book f1 f2
    return $ Rwt e' f'

  (Met n1 t1 xs1, Met n2 t2 xs2) | n1 == n2 && length xs1 == length xs2 -> do
    t' <- unifyTerms d book t1 t2
    xs' <- mapM (uncurry (unifyTerms d book)) (zip xs1 xs2)
    return $ Met n1 t' xs'

  (Sup l1 a1 b1, Sup l2 a2 b2) -> do
    l' <- unifyTerms d book l1 l2
    a' <- unifyTerms d book a1 a2
    b' <- unifyTerms d book b1 b2
    return $ Sup l' a' b'

  (SupM l1 f1, SupM l2 f2) -> do
    l' <- unifyTerms d book l1 l2
    f' <- unifyTerms d book f1 f2
    return $ SupM l' f'

  (Log s1 x1, Log s2 x2) -> do
    s' <- unifyTerms d book s1 s2
    x' <- unifyTerms d book x1 x2
    return $ Log s' x'

  (Frk l1 a1 b1, Frk l2 a2 b2) -> do
    l' <- unifyTerms d book l1 l2
    a' <- unifyTerms d book a1 a2
    b' <- unifyTerms d book b1 b2
    return $ Frk l' a' b'

  -- If they're equal, return either
  (t1, t2) | eql False d book t1 t2 -> Just t1

  -- Otherwise, conflict
  _ -> Nothing

-- Type inference with fallback to indirect inference
-- 1) First attempts structural inference (inferStructural)
-- 2) For lambdas without type annotations, uses inferIndirect
-- 3) For other failures, uses environment hint (with inferIndirect) if provided
--
-- Returns: inferred type, or Fail if cannot infer
infer :: Int -> Span -> Book -> Ctx -> Term -> Maybe Term -> Result Term
infer d span book ctx term environment = 
  case inferStructural d span book ctx term of
    Done t -> 
      -- trace ("infered " ++ show term ++ " :: " ++ show t) $ 
      return t
    Fail (CantInfer _ _ _) -> case cut term of
      Lam k mt b -> case mt of
        Just t -> do -- already tried by inferStructural
          Fail $ CantInfer span (normalCtx book ctx) Nothing
        Nothing -> do
          t <- inferIndirect (d+1) span book ctx (Var k d) (b (Var k d))
          bT <- inferStructural (d+1) span book (extend ctx k (Var k d) t) (b (Var k d)) -- could this be infer?
          let res = All t (Lam k (Just t) (\v -> bindVarByIndex d v bT))
          -- trace ("infered " ++ show term ++ " :: " ++ show res) $ return res
          return $ All t (Lam k (Just t) (\v -> bindVarByIndex d v bT))
      _ -> case environment of 
        Just env -> do
          -- res <- inferIndirect d span book ctx term env
          -- trace ("infered " ++ show term ++ " :: " ++ show res) $ return res
          inferIndirect d span book ctx term env
        _        -> Fail $ CantInfer span (normalCtx book ctx) Nothing
    e -> e

-- Direct structural type inference
-- 1) Follows standard inference rules for each term constructor (e.g. term = Bit0 implies term : Bit)
-- 2) Handles special cases for dependent types (Sig, All)
-- 3) For applications, checks function type and applies
-- 4) Cannot infer: Fix, Tst, EmpM, UniM, BitM, etc. (eliminators)
--
-- Returns: inferred type based on term structure
inferStructural :: Int -> Span -> Book -> Ctx -> Term -> Result Term
inferStructural d span book@(Book defs names) ctx term =
  case term of

    -- x : T in ctx
    -- ------------ infer-Var
    -- ctx |- x : T
    Var k i -> do
      let Ctx ks = ctx
      if i < length ks
        then let (_, _, typ) = ks !! i
             in return typ
        else Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- x:T in book
    -- ------------ infer-Ref
    -- ctx |- x : T
    Ref k i -> do
      case getDefn book k of
        Just (_, _, typ) -> return typ
        Nothing          -> Fail $ Undefined span (normalCtx book ctx) k Nothing

    -- ctx |- x : T
    -- ------------ infer-Sub
    -- ctx |- x : T
    Sub x -> do
      inferStructural d span book ctx x

    -- ctx        |- t : Set
    -- ctx        |- v : t
    -- ctx, v : T |- f : T
    -- -------------------------- infer-Let
    -- ctx |- (k : T = v ; f) : T
    Let k t v f -> case t of
      Just t -> do
        _ <- check d span book ctx t Set
        _ <- check d span book ctx v t
        inferStructural (d+1) span book (extend ctx k (Var k d) t) (f (Var k d))
      Nothing -> do
        vT <- inferStructural d span book ctx v
        inferStructural (d+1) span book (extend ctx k (Var k d) vT) (f (Var k d))

    -- ctx |- f(v) : T
    -- -------------------------- infer-Use
    -- ctx |- (use k = v ; f) : T
    Use k v f -> do
      inferStructural d span book ctx (f v)

    -- Can't infer Fix
    Fix k f -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |- t : Set
    -- ctx |- v : t
    -- ------------------- infer-Chk
    -- ctx |- (v :: t) : t
    Chk v t -> do
      _ <- check d span book ctx t Set
      _ <- check d span book ctx v t
      return t
    
    -- Can't infer Trust
    Tst _ -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |-
    -- ---------------- Set
    -- ctx |- Set : Set
    Set -> do
      return Set

    -- ctx |-
    -- ------------------ Emp
    -- ctx |- Empty : Set
    Emp -> do
      return Set

    -- Can't infer EmpM
    EmpM -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |-
    -- ----------------- Uni
    -- ctx |- Unit : Set
    Uni -> do
      return Set

    -- ctx |-
    -- ---------------- One
    -- ctx |- () : Unit
    One -> do
      return Uni

    -- Can't infer UniM
    UniM f -> do
      fT <- inferStructural d span book ctx f
      return $ All Uni (UniM fT) 

    -- ctx |-
    -- ----------------- Bit
    -- ctx |- Bool : Set
    Bit -> do
      return Set

    -- ctx |-
    -- ------------------- Bt0
    -- ctx |- False : Bool
    Bt0 -> do
      return Bit

    -- ctx |-
    -- ------------------ Bt1
    -- ctx |- True : Bool
    Bt1 -> do
      return Bit

    -- Can't infer BitM
    BitM f t -> do
      fT <- inferStructural d span book ctx f
      tT <- inferStructural d span book ctx t
      return $ All Bit (BitM fT tT)
      -- Fail $ CantInfer span (normalCtx book ctx)

    -- ctx |-
    -- ---------------- Nat
    -- ctx |- Nat : Set
    Nat -> do
      return Set

    -- ctx |-
    -- --------------- Zer
    -- ctx |- 0n : Nat
    Zer -> do
      return Nat

    -- ctx |- n : Nat
    -- ----------------- Suc
    -- ctx |- 1n+n : Nat
    Suc n -> do
      _ <- check d span book ctx n Nat
      return Nat

    NatM z s -> do
      case cut s of
        Lam p mtp bp -> do
          zT <- inferStructural d span book ctx z
          sT <- inferStructural d span book (extend ctx p (Var p d) Nat) (bp (Var p d))
          return $ All Nat (NatM zT (Lam p (Just Nat) (\_ -> sT)))
        _ -> do
          zT <- inferStructural d span book ctx z
          sT <- inferStructural d span book ctx s
          return $ All Nat (NatM zT sT)
      -- Fail $ CantInfer span (normalCtx book ctx)

    -- ctx |- T : Set
    -- ---------------- Lst
    -- ctx |- T[] : Set
    Lst t -> do
      _ <- check d span book ctx t Set
      return Set

    -- Can't infer Nil
    Nil -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- Can't infer Con
    Con h t -> do
      hT <- inferStructural d span book ctx h
      _ <- check d span book ctx t (Lst hT)
      return $ Lst hT
      -- Fail $ CantInfer span (normalCtx book ctx)

    -- Can't infer LstM
    LstM n c -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |-
    -- ---------------------- Enu
    -- ctx |- enum{...} : Set
    Enu s -> do
      return Set

    -- ctx |- &s in enum{...}
    -- ---------------------- Sym
    -- ctx |- &s : enum{...}
    Sym s -> do
      let bookEnums = [ Enu tags | (k, (_, (Sig (Enu tags) _), Set)) <- M.toList defs ]
      case find isEnuWithTag bookEnums of
        Just t  -> return t
        Nothing -> Fail $ Undefined span (normalCtx book ctx) ("@" ++ s) Nothing
        where
          isEnuWithTag (Enu tags) = s `elem` tags
          isEnuWithTag _ = False

    -- Can't infer EnuM
    EnuM cs e -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |- A : Set
    -- ctx |- B : ∀x:A. Set
    -- -------------------- Sig
    -- ctx |- ΣA.B : Set
    Sig a b -> do
      _ <- check d span book ctx a Set
      _ <- check d span book ctx b (All a (Lam "_" Nothing (\_ -> Set)))
      return Set

    -- ctx |- a : A
    -- ctx |- b : B
    -- --------------------- Tup
    -- ctx |- (a,b) : Σx:A.B
    Tup (cut -> Sym s) b -> do
      let candidates = [ t | (k, (_, t@(Sig (Enu tags) _), Set)) <- M.toList defs, s `elem` tags ]
      case candidates of
        [t] -> do
          t' <- check d span book ctx t Set
          _  <- check d span book ctx term t'
          return t'
        _ -> Fail $ CantInfer span (normalCtx book ctx) Nothing
    Tup a b -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- Can't infer SigM
    SigM f -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |- A : Set
    -- ctx |- B : ∀x:A. Set
    -- -------------------- All
    -- ctx |- ∀A.B : Set
    All a b -> do
      _ <- check d span book ctx a Set
      _ <- check d span book ctx b (All a (Lam "_" Nothing (\_ -> Set)))
      return Set

    -- ctx |- A : Set
    -- ctx, x:A |- f : B
    -- ------------------------ Lam
    -- ctx |- λx:A. f : ∀x:A. B
    Lam k t b -> case t of
      Just tk -> do
        _ <- check d span book ctx tk Set
        bT <- inferStructural (d+1) span book (extend ctx k (Var k d) tk) (b (Var k d))
        return (All tk (Lam k (Just tk) (\v -> bindVarByIndex d v bT)))
      Nothing -> do
        Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |- f : ∀x:A. B
    -- ctx |- x : A
    -- ------------------ App
    -- ctx |- f(x) : B(x)
    App f x -> do
      case cut f of
        -- UniM b -> do
        --   check d span book ctx x Uni
        --   -- bT <- infer d span book ctx b
        --   bT <- infer d span book (specializeCtx book x Bt0 ctx) b
        --   Done bT
        --
        -- BitM f t -> do
        --   check d span book ctx x Bit
        --   -- fT <- infer d span book ctx f
        --   -- tT <- infer d span book ctx t
        --   fT <- infer d span book (specializeCtx book x Bt0 ctx) f
        --   tT <- infer d span book (specializeCtx book x Bt1 ctx) t
        --   if equal d book fT tT
        --   then Done $ fT
        --   else Done $ App (BitM fT tT) x
        --
        -- NatM z (cut -> Lam k mt b) -> do
        --   check d span book ctx x Nat
        --   zT <- infer d span book ctx z
        --   -- sT <- infer (d+1) span book (extend ctx k (Var k d) Nat) (b (Var k d))
        --   sT <- infer (d+1) span book (extend (specializeCtx book x (Suc (Var k d)) ctx) k (Var k d) Nat) (b (Var k d))
        --   if equal d book sT zT
        --   then Done $ zT
        --   else Done $ App (NatM zT (Lam k (Just Nat) (\v -> bindVarByIndex d v sT))) x
        --
        -- LstM n c -> do
        --   xT <- infer d span book ctx x
        --   case cut xT of
        --     Lst hT -> do
        --       nT <- infer d span book ctx n
        --       case cut c of
        --         Lam h mth bh -> do
        --           let body_h = (bh (Var h d))
        --           case cut body_h of
        --             Lam t mtt bt -> do
        --               -- cT <- infer (d+2) span book (extend (extend ctx h (Var h d) hT) t (Var t (d+1)) (Lst hT)) (bt (Var t (d+1)))
        --               cT <- infer (d+2) span book (extend (extend (specializeCtx book x (Con (Var h d) (Var t (d+1))) ctx) h (Var h d) hT) t (Var t (d+1)) (Lst hT)) (bt (Var t (d+1)))
        --               if equal d book nT cT
        --               then Done nT
        --               else Done $ App (LstM nT (Lam h (Just hT) (\v -> bindVarByIndex d v (Lam t (Just (Lst hT)) (\v2 -> bindVarByIndex (d+1) v2 cT))))) x
        --             _ -> Fail $ CantInfer (getSpan span body_h) (normalCtx book ctx)
        --         _ -> Fail $ CantInfer (getSpan span c) (normalCtx book ctx)
        --     hT -> Fail $ TypeMismatch (getSpan span x) (normalCtx book ctx) (normal book (Lst (Var "_" 0))) (normal book hT)
        --
        --
        -- SigM g -> do -- TODO: complete the Tup case \/
        --   xTinfer <- case cut x of
        --     _ -> do
        --       xTinfer <- inferStructural d span book ctx x
        --       Done $ derefADT xTinfer
        --         where
        --           derefADT trm = case cut trm of
        --             Ref k i ->
        --               let xTbody = getDefn book k in
        --               case xTbody of
        --                 Just (_, cut -> bod@(Sig (cut -> Enu _) _), _) -> bod
        --                 _ -> trm
        --             _ -> trm
        --   let xT = case cut xTinfer of -- when the Sig is from modeling an ADT, use the ADT explicitly
        --         Ref k i -> case getDefn book k of
        --           Just (_,cut -> y@(Sig (cut -> Enu _) _),_) -> y
        --           _ -> normal book xTinfer
        --         _ -> normal book xTinfer
        --   case cut g of
        --     Lam a mta ab ->
        --       case cut (ab (Var a d)) of
        --         Lam b mtb bb -> do
        --           case cut xT of
        --             Sig aT bFunc -> do
        --               -- if so, use the the dependent type of x (i.e. Σa:aT.bT(a)) to infer about the type of `body` with `b : bT(a)`
        --               case cut bFunc of
        --                 Lam kaT mtatv bFuncBod -> do
        --                   -- traceM ("bT in SIG: " ++ show (App bFunc (Var a d)) ++ " --from-- " ++ show term ++ "\n-ctx:\n"++show ctx ++ "\n")
        --                   -- check that aT and bT are types, and if so, proceed to infer the type of `body` (here denoted bb)
        --                   let aV = case cut x of
        --                           Tup l r -> l
        --                           _       -> Var a d
        --                   let bV = case cut x of
        --                           Tup l r -> r
        --                           _       -> Var b (d+1)
        --                   let bT = (App bFunc aV)
        --                   _ <- check d span book ctx aT Set
        --                   _ <- check (d+1) span book (extend ctx a aV aT) bT Set
        --                   inferStructural (d+2) span book (extend (extend ctx a aV aT) b bV (normal book bT)) (rewrite d book (Var a d) aV (bb bV))
        --
        --                 _ -> Fail $ CantInfer (getSpan span bFunc) (normalCtx book ctx) Nothing
        --             App f' x' | equal d book x' x -> do
        --               Fail $ CantInfer (getSpan span term) (normalCtx book ctx) Nothing
        --             _ -> do
        --               -- traceM ("Will fail infer " ++ show term ++ " with xT = " ++ show (normal book xT) ++ " and ctx: \n" ++ show ctx)
        --               Fail $ TypeMismatch (getSpan span x) (normalCtx book ctx) (Var "Σ_:_ . _" 0) xT Nothing
        --         _ -> Fail $ CantInfer (getSpan span (ab (Var a d))) (normalCtx book ctx) Nothing
        --     _ -> Fail $ CantInfer (getSpan span g) (normalCtx book ctx) Nothing

        -- SigM g -> do -- TODO: complete the Tup case \/
        --   case cut x of
        --     -- can't infer a dependent type from a single tuple
        --     Tup _ _ -> Fail $ CantInfer (getSpan span x) (normalCtx book ctx)
        --     -- is `(App (SigM g) x)` some `λ{(,): λa.λb. body}(x)` with `x : Some_Dependent_Pair_Type`?
        --     x_cut ->
        --       case cut g of
        --         Lam a mta ab ->
        --           case cut (ab (Var a d)) of
        --             Lam b mtb bb -> do
        --               xTinfer <- infer d span book ctx x 
        --               xTinfer <- infer d span book ctx x 
        --               let xT = case cut xTinfer of -- when the Sig is from modeling an ADT, use the ADT explicitly
        --                     Ref k i -> case getDefn book k of
        --                       Just (_,cut -> y@(Sig (cut -> Enu _) _),_) -> y
        --                       _ -> normal book xTinfer
        --                     _ -> normal book xTinfer
        --
        --               -- traceM ("inferring " ++ show term ++ " with typeof(" ++ show x ++"): " ++ show xT)
        --               case cut xT of
        --                 Sig aT bFunc -> do
        --                   -- if so, use the the dependent type of x (i.e. Σa:aT.bT(a)) to infer about the type of `body` with `b : bT(a)`
        --                   case cut bFunc of
        --                     Lam kaT mtatv bFuncBod -> do
        --                       -- traceM ("bT in SIG: " ++ show (App bFunc (Var a d)) ++ " --from-- " ++ show term ++ "\n-ctx:\n"++show ctx ++ "\n")
        --                       let bT = (App bFunc (Var a d))
        --                       -- check that aT and bT are types, and if so, proceed to infer the type of `body` (here denoted bb)
        --                       check d span book ctx aT Set
        --                       check (d+1) span book (extend ctx a (Var a d) aT) bT Set
        --                       infer (d+2) span book (extend (extend ctx a (Var a d) aT) b (Var b (d+1)) (normal book bT)) (bb (Var b (d+1))) 
        --
        --                     _ -> Fail $ CantInfer (getSpan span bFunc) (normalCtx book ctx)
        --                 App f' x' | equal d book x' x -> do
        --                   Fail $ CantInfer (getSpan span term) (normalCtx book ctx)
        --                 _ -> do
        --                   -- traceM ("Will fail infer " ++ show term ++ " with xT = " ++ show (normal book xT) ++ " and ctx: \n" ++ show ctx)
        --                   Fail $ TypeMismatch (getSpan span x) (normalCtx book ctx) (Var "Σ_:_ . _" 0) xT
        --             _ -> Fail $ CantInfer (getSpan span (ab (Var a d))) (normalCtx book ctx)
        --         _ -> Fail $ CantInfer (getSpan span g) (normalCtx book ctx)
        --
        -- EnuM cs Nothing -> do
        --   xT <- infer d span book ctx x
        --   case normal book xT of
        --     Enu syms -> do
        --       let mbY = listToMaybe [(ks,func) | (_, (_, Sig (Enu ks) func, _)) <- M.toList defs, ks == syms]
        --       case mbY of 
        --         Just (ks, func) | ks == syms -> do
        --           -- traceM ("about to infer all csTypes with\n ks: " ++ show ks ++ "\n func: " ++ show func)
        --           -- traceM (" cases: " ++ show cs)
        --           -- traceM (" term: " ++ show term)
        --           csTypes <- mapM (\(s, t) -> do { ty <- infer d span book (specializeCtx book x (Sym s) ctx) t; return (s, ty) }) cs
        --           traceM (" csTypes: " ++ show csTypes ++ "\n")
        --           Done $ App (EnuM csTypes Nothing) x
        --
        --           -- let allEqual = case csTypes of { [] -> True; ((_,t):rest) -> all (\(_,t') -> equal d book t t') rest }
        --           --     res = App (EnuM csTypes Nothing) x
        --           -- if allEqual
        --           -- then Done res
        --           -- else Done res
        --         _ -> do
        --           traceM ("can't infer EnuM: " ++ show term ++ " after finding mbY = " ++ show mbY)
        --           Fail $ CantInfer (getSpan span term) (normalCtx book ctx)
        --     _ -> Fail $ CantInfer (getSpan span term) (normalCtx book ctx)

        f -> do
          fT <- inferStructural d span book ctx f
          case force book fT of
            All fA fB -> do
              _ <- check d span book ctx x fA
              return (App fB x)
            _ -> do
              Fail $ TypeMismatch span (normalCtx book ctx) (normal book (All (Var "_" 0) (Lam "_" Nothing (\_ -> Var "_" 0)))) (normal book fT) Nothing

    -- ctx |- t : Set
    -- ctx |- a : t
    -- ctx |- b : t
    -- ---------------------- Eql
    -- ctx |- t{a == b} : Set
    Eql t a b -> do
      _ <- check d span book ctx t Set
      _ <- check d span book ctx a t
      _ <- check d span book ctx b t
      return Set

    -- Can't infer Rfl
    Rfl -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- Can't infer EqlM
    EqlM f -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |- e : t{a==b}
    -- ctx[a <- b] |- f : T[a <- b]
    -- ---------------------------- Rwt
    -- ctx |- rewrite e f : T
    Rwt e f -> do
      eT <- inferStructural d span book ctx e
      case force book eT of
        Eql t a b -> do
          let rewrittenCtx = rewriteCtx d book a b ctx
          inferStructural d span book rewrittenCtx f
        _ ->
          Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0))) (normal book eT) Nothing

    -- ctx |- t : T
    -- ------------ Loc
    -- ctx |- t : T
    Loc l t ->
      inferStructural d l book ctx t

    -- Can't infer Era
    Era -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- Can't infer Sup
    Sup l a b -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- Can't infer SupM
    SupM l f -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- Can't infer Frk
    Frk l a b -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- Can't infer Met
    Met n t c -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |-
    -- -------------- Num
    -- ctx |- T : Set
    Num t -> do
      return Set

    -- ctx |-
    -- -------------- Val-U64
    -- ctx |- n : U64
    Val (U64_V v) -> do
      return (Num U64_T)

    -- ctx |-
    -- -------------- Val-I64
    -- ctx |- n : I64
    Val (I64_V v) -> do
      return (Num I64_T)

    -- ctx |-
    -- -------------- Val-F64
    -- ctx |- n : F64
    Val (F64_V v) -> do
      return (Num F64_T)

    -- ctx |-
    -- --------------- Val-CHR
    -- ctx |- c : Char
    Val (CHR_V v) -> do
      return (Num CHR_T)

    -- ctx |- a : ta
    -- ctx |- b : tb
    -- inferOp2Type op ta tb = tr
    -- --------------------------- Op2
    -- ctx |- a op b : tr
    Op2 op a b -> do
      ta <- inferStructural d span book ctx a
      tb <- inferStructural d span book ctx b
      inferOp2Type d span book ctx op ta tb

    -- ctx |- a : ta
    -- inferOp1Type op ta = tr
    -- ----------------------- Op1
    -- ctx |- op a : tr
    Op1 op a -> do
      ta <- inferStructural d span book ctx a
      inferOp1Type d span book ctx op ta

    -- ctx |-
    -- -------------------------------- Pri-U64_TO_CHAR
    -- ctx |- U64_TO_CHAR : U64 -> Char
    Pri U64_TO_CHAR -> do
      return (All (Num U64_T) (Lam "x" Nothing (\_ -> Num CHR_T)))

    -- ctx |-
    -- -------------------------------- Pri-CHAR_TO_U64
    -- ctx |- CHAR_TO_U64 : Char -> U64
    Pri CHAR_TO_U64 -> do
      return (All (Num CHR_T) (Lam "x" Nothing (\_ -> Num U64_T)))

    -- Can't infer HVM priority change primitives
    Pri HVM_INC -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing
    Pri HVM_DEC -> do
      Fail $ CantInfer span (normalCtx book ctx) Nothing

    -- ctx |- s : Char[]
    -- ctx |- x : T
    -- ------------------ Log
    -- ctx |- log s x : T
    Log s x -> do
      _ <- check d span book ctx s (Lst (Num CHR_T))
      inferStructural d span book ctx x

    -- Not supported in infer
    Pat _ _ _ -> do
      error "Pat not supported in infer"

-- Infer the result type of a binary numeric operation
inferOp2Type :: Int -> Span -> Book -> Ctx -> NOp2 -> Term -> Term -> Result Term
inferOp2Type d span book ctx op ta tb = do
  -- For arithmetic ops, both operands must have the same numeric type
  case op of
    ADD -> numericOp ta tb
    SUB -> numericOp ta tb
    MUL -> numericOp ta tb
    DIV -> numericOp ta tb
    MOD -> numericOp ta tb
    POW -> numericOp ta tb
    -- Comparison ops return Bool
    EQL -> comparisonOp ta tb
    NEQ -> comparisonOp ta tb
    LST -> comparisonOp ta tb
    GRT -> comparisonOp ta tb
    LEQ -> comparisonOp ta tb
    GEQ -> comparisonOp ta tb
    -- Bitwise/logical ops work on both integers and booleans
    AND -> boolOrIntegerOp ta tb
    OR  -> boolOrIntegerOp ta tb
    XOR -> boolOrIntegerOp ta tb
    SHL -> integerOp ta tb
    SHR -> integerOp ta tb
  where
    numericOp ta tb = case (force book ta, force book tb) of
      (Num t1, Num t2) | t1 == t2 -> return (Num t1)
      (Nat, Nat) -> return Nat  -- Allow Nat arithmetic operations
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Ref "Num" 1)) (normal book ta) Nothing

    comparisonOp ta tb = case (force book ta, force book tb) of
      (Num t1, Num t2) | t1 == t2 -> return Bit
      (Bit, Bit) -> return Bit  -- Allow Bool comparison
      (Nat, Nat) -> return Bit  -- Allow Nat comparison
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book ta) (normal book tb) Nothing

    integerOp ta tb = case (force book ta, force book tb) of
      (Num U64_T, Num U64_T) -> return (Num U64_T)
      (Num I64_T, Num I64_T) -> return (Num U64_T)  -- Bitwise on I64 returns U64
      (Num F64_T, Num F64_T) -> return (Num U64_T)  -- Bitwise on F64 returns U64
      (Num CHR_T, Num CHR_T) -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Ref "Num" 1)) (normal book ta)  Nothing -- Bitwise not supported for CHR
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Ref "Num" 1)) (normal book ta) Nothing

    boolOrIntegerOp ta tb = case (force book ta, force book tb) of
      (Bit, Bit) -> return Bit  -- Logical operations on booleans
      (Num U64_T, Num U64_T) -> return (Num U64_T)  -- Bitwise operations on integers
      (Num I64_T, Num I64_T) -> return (Num U64_T)
      (Num F64_T, Num F64_T) -> return (Num U64_T)
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book ta) (normal book tb) Nothing

-- Infer the result type of a unary numeric operation
inferOp1Type :: Int -> Span -> Book -> Ctx -> NOp1 -> Term -> Result Term
inferOp1Type d span book ctx op ta = case op of
  NOT -> case force book ta of
    Bit       -> return Bit  -- Logical NOT on Bool
    Num U64_T -> return (Num U64_T)
    Num I64_T -> return (Num U64_T)  -- Bitwise NOT on I64 returns U64
    Num F64_T -> return (Num U64_T)  -- Bitwise NOT on F64 returns U64
    Num CHR_T -> Fail $ CantInfer span (normalCtx book ctx) Nothing -- Bitwise NOT not supported for CHR
    _         -> Fail $ CantInfer span (normalCtx book ctx) Nothing
  NEG -> case force book ta of
    Num I64_T -> return (Num I64_T)
    Num F64_T -> return (Num F64_T)
    Num CHR_T -> Fail $ CantInfer span (normalCtx book ctx) Nothing -- Negation not supported for CHR
    _         -> Fail $ CantInfer span (normalCtx book ctx) Nothing

---- Bidirectional type checking with term transformation
-- 1) Verifies term has expected type 'goal'
-- 2) May transform term (i.e. by splitting eliminator applications to application of aux functions)
-- 3) Handles equality types specially (Eql with Suc, Con, etc.)
-- 4) For eliminators as functions, introduces auxiliary definitions
--
-- Application splitting example:
--   (App (NatM z s) x) : T
--   becomes: 
--   (Let $aux : (∀x:Nat. T) = (NatM z s) in (App $aux x))
--
-- Returns: possibly transformed term that has type 'goal'
check :: Int -> Span -> Book -> Ctx -> Term -> Term -> Result Term
check d span book ctx (Loc l t) goal = do
  t' <- check d l book ctx t goal 
  return $ Loc l t'
check d span book ctx term      goal =
  -- trace ("- check: " ++ show d ++ " " ++ show term ++ " :: " ++ show (normal book goal)) $
  -- trace ("- check: " ++ show d ++ " " ++ show term ++ " :: " ++ show (normal book goal) ++ " ::: span: " ++ show span) $
  -- trace ("- check: " ++ show d ++ " " ++ show term ++ " :: " ++ show (normal book goal) ++ "\n- ctx:\n" ++ show ctx ++ "\n") $
  let nGoal = force book goal in
  case (term, nGoal) of
    -- ctx |-
    -- ------------------ Trust
    -- ctx |- trust x : T
    (Tst _, _) -> do
      return term

    -- ctx |- 
    -- ----------- Era
    -- ctx |- * : T
    (Era, _) -> do
      return term

    -- ctx |- t : Set
    -- ctx |- v : t
    -- ctx, x:t |- f : T
    -- ------------------------- Let
    -- ctx |- (x : t = v ; f) : T
    (Let k t v f, _) -> case t of
        Just t  -> do
          t' <- check d span book ctx t Set
          v' <- check d span book ctx v t
          f' <- check (d+1) span book (extend ctx k (Var k d) t') (f (Var k d)) goal
          return $ Let k (Just t') v' (\x -> bindVarByName k x f')
        Nothing -> do
          t <- infer d span book ctx v Nothing
          t' <- check d span book ctx t Set
          v' <- cutChk <$> check d span book ctx v t
          f' <- check (d+1) span book (extend ctx k (Var k d) t') (f (Var k d)) goal
          return $ Let k (Just t') v' (\x -> bindVarByName k x f')

    -- ctx |- f(v) : T
    -- -------------------------- Use
    -- ctx |- (use k = v ; f) : T
    (Use k v f, _) -> do
      check d span book ctx (f v) goal

    -- ctx |- 
    -- ---------------- One
    -- ctx |- () : Unit
    (One, Uni) -> do
      return term

    -- ctx |- 
    -- ------------------- Bt0
    -- ctx |- False : Bool
    (Bt0, Bit) -> do
      return term

    -- ctx |- 
    -- ------------------ Bt1
    -- ctx |- True : Bool
    (Bt1, Bit) -> do
      return term

    -- ctx |- 
    -- --------------- Zer
    -- ctx |- 0n : Nat
    (Zer, Nat) -> do
      return term

    -- ctx |- n : Nat
    -- ----------------- Suc
    -- ctx |- 1n+n : Nat
    (Suc n, Nat) -> do
      n' <- 
        check d span book ctx n Nat
      return $ Suc n'

    -- ctx |- n : t{a==b}
    -- --------------------------- Suc-Eql
    -- ctx |- 1n+n : t{1n+a==1n+b}
    (Suc n, Eql t (force book -> Suc a) (force book -> Suc b)) -> do
      n' <- 
        check d span book ctx n (Eql t a b)
      return $ 
        Suc n'

    -- ctx |- 
    -- --------------- Nil
    -- ctx |- [] : T[]
    (Nil, Lst t) -> do
      return term

    -- Type mismatch for Nil
    (Nil, goal) ->
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Lst (Var "_" 0))) (normal book goal) Nothing

    -- ctx |- h : T
    -- ctx |- t : T[]
    -- ------------------ Con
    -- ctx |- h<>t : T[]
    (Con h t, Lst tT) -> do
      h' <- check d span book ctx h tT
      t' <- check d span book ctx t (Lst tT)
      return $ Con h' t'

    -- ctx |- h : T{h1==h2}
    -- ctx |- t : T[]{t1==t2}
    -- --------------------------------- Con-Eql
    -- ctx |- h<>t : T[]{h1<>t1==h2<>t2}
    (Con h t, Eql (force book -> Lst tT) (force book -> Con h1 t1) (force book -> Con h2 t2)) -> do
      h' <- check d span book ctx h (Eql tT h1 h2)
      t' <- check d span book ctx t (Eql (Lst tT) t1 t2)
      return $ Con h' t'

    -- ctx, x:A |- f : B
    -- ---------------------- Lam
    -- ctx |- λx. f : ∀x:A. B
    (Lam k t f, All a b) -> do
      f' <- check (d+1) span book (extend ctx k (Var k d) a) (f (Var k d)) (App b (Var k d))
      return $ Lam k t (\v -> bindVarByIndex d v f')

    -- ctx |- 
    -- --------------------------------- EmpM-Eql-Zer-Suc
    -- ctx |- λ{} : ∀p:t{0n==1n+y}. R(p)
    (EmpM, All (force book -> Eql t (force book -> Zer) (force book -> Suc y)) rT) -> do
      return term

    -- ctx |- 
    -- --------------------------------- EmpM-Eql-Suc-Zer
    -- ctx |- λ{} : ∀p:t{1n+x==0n}. R(p)
    (EmpM, All (force book -> Eql t (force book -> Suc x) (force book -> Zer)) rT) -> do
      return term

    -- ctx |- λ{} : ∀p:t{x==y}. R(p)
    -- ----------------------------------- EmpM-Eql-Suc-Suc
    -- ctx |- λ{} : ∀p:t{1n+x==1n+y}. R(p)
    (EmpM, All (force book -> Eql t (force book -> Suc x) (force book -> Suc y)) rT) -> do
      check d span book ctx EmpM (All (Eql t x y) rT)

    -- ctx |- 
    -- ------------------------ EmpM-Emp
    -- ctx |- λ{} : ∀x:Empty. R
    (EmpM, All (force book -> Emp) rT) -> do
      return term

    -- Type mismatch for EmpM
    (EmpM, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Emp (Lam "_" Nothing (\_ -> (Var "?" 0))))) Nothing

    -- ctx |- f : R({==})
    -- -------------------------------------- UniM-Eql
    -- ctx |- λ{():f} : ∀p:Unit{()==()}. R(p)
    (UniM f, All (force book -> Eql (force book -> Uni) (force book -> One) (force book -> One)) rT) -> do
      f' <- check d span book ctx f (App rT Rfl)
      return $ UniM f'

    -- ctx |- f : R(())
    -- --------------------------- UniM
    -- ctx |- λ{():f} : ∀x:Unit. R
    (UniM f, All (force book -> Uni) rT) -> do
      f' <- check d span book ctx f (App rT One)
      return $ UniM f'

    -- Type mismatch for UniM
    (UniM f, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Uni (Lam "_" Nothing (\_ -> (Var "?" 0))))) Nothing

    -- ctx |- f : R({==})
    -- ------------------------------------------------------ BitM-Eql-Bt0-Bt0
    -- ctx |- λ{False:f;True:t} : ∀p:Bool{False==False}. R(p)
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt0) (force book -> Bt0)) rT) -> do
      f' <- check d span book ctx f (App rT Rfl)
      return $ BitM f' t

    -- ctx |- t : R({==})
    -- ---------------------------------------------------- BitM-Eql-Bt1-Bt1
    -- ctx |- λ{False:f;True:t} : ∀p:Bool{True==True}. R(p)
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt1) (force book -> Bt1)) rT) -> do
      t' <- check d span book ctx t (App rT Rfl)
      return $ BitM f t'

    -- ctx |- 
    -- ----------------------------------------------------- BitM-Eql-Bt0-Bt1
    -- ctx |- λ{False:f;True:t} : ∀p:Bool{False==True}. R(p)
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt0) (force book -> Bt1)) rT) -> do
      return term

    -- ctx |- 
    -- ----------------------------------------------------- BitM-Eql-Bt1-Bt0
    -- ctx |- λ{False:f;True:t} : ∀p:Bool{True==False}. R(p)
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt1) (force book -> Bt0)) rT) -> do
      return term

    -- ctx |- f : R(False)
    -- ctx |- t : R(True)
    -- ------------------------------------- BitM
    -- ctx |- λ{False:f;True:t} : ∀x:Bool. R
    (BitM f t, All (force book -> Bit) rT) -> do
      f' <- check d span book ctx f (App rT Bt0)
      t' <- check d span book ctx t (App rT Bt1)
      return $ BitM f' t'

    -- Type mismatch for BitM
    (BitM f t, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Bit (Lam "_" Nothing (\_ -> (Var "?" 0))))) Nothing

    -- ctx |- z : R({==})
    -- ------------------------------------------- NatM-Eql-Zer-Zer
    -- ctx |- λ{0n:z;1n+:s} : ∀p:Nat{0n==0n}. R(p)
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Zer) (force book -> Zer)) rT) -> do
      z' <- check d span book ctx z (App rT Rfl)
      return $ NatM z' s

    -- ctx |- s : ∀p:Nat{a==b}. R(1n+p)
    -- ----------------------------------------------- NatM-Eql-Suc-Suc
    -- ctx |- λ{0n:z;1n+:s} : ∀p:Nat{1n+a==1n+b}. R(p)
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Suc a) (force book -> Suc b)) rT) -> do
      s' <- check d span book ctx s (All (Eql Nat a b) (Lam "p" Nothing (\p -> App rT (Suc p))))
      return $ NatM z s'

    -- ctx |- 
    -- --------------------------------------------- NatM-Eql-Zer-Suc
    -- ctx |- λ{0n:z;1n+:s} : ∀p:Nat{0n==1n+_}. R(p)
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Zer) (force book -> Suc _)) rT) -> do
      return term

    -- ctx |- 
    -- --------------------------------------------- NatM-Eql-Suc-Zer
    -- ctx |- λ{0n:z;1n+:s} : ∀p:Nat{1n+_==0n}. R(p)
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Suc _) (force book -> Zer)) rT) -> do
      return term

    -- ctx |- z : R(0n)
    -- ctx |- s : ∀p:Nat. R(1n+p)
    -- -------------------------------- NatM
    -- ctx |- λ{0n:z;1n+:s} : ∀x:Nat. R
    (NatM z s, All (force book -> Nat) rT) -> do
      z' <- check d span book ctx z (App rT Zer)
      s' <- check d span book ctx s (All Nat (Lam "p" Nothing (\p -> App rT (Suc p))))
      return $ NatM z' s'

    -- Type mismatch for NatM
    (NatM z s, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Nat (Lam "_" Nothing (\_ -> (Var "?" 0))))) Nothing

    -- ctx |- n : R({==})
    -- ------------------------------------------ LstM-Eql-Nil-Nil
    -- ctx |- λ{[]:n;<>:c} : ∀p:T[]{[]==[]}. R(p)
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Nil) (force book -> Nil)) rT) -> do
      n' <- check d span book ctx n (App rT Rfl)
      return $ LstM n' c

    -- ctx |- c : ∀hp:T{h1==h2}. ∀tp:T[]{t1==t2}. R(hp<>tp)
    -- ---------------------------------------------------- LstM-Eql-Con-Con
    -- ctx |- λ{[]:n;<>:c} : ∀p:T[]{h1<>t1==h2<>t2}. R(p)
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Con h1 t1) (force book -> Con h2 t2)) rT) -> do
      c' <- check d span book ctx c (All (Eql a h1 h2) (Lam "hp" Nothing (\hp -> 
        All (Eql (Lst a) t1 t2) (Lam "tp" Nothing (\tp -> 
          App rT (Con hp tp))))))
      return $ LstM n c'

    -- ctx |- 
    -- -------------------------------------------- LstM-Eql-Nil-Con
    -- ctx |- λ{[]:n;<>:c} : ∀p:T[]{[]==_<>_}. R(p)
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Nil) (force book -> Con _ _)) rT) -> do
      return term

    -- ctx |- 
    -- -------------------------------------------- LstM-Eql-Con-Nil
    -- ctx |- λ{[]:n;<>:c} : ∀p:T[]{_<>_==[]}. R(p)
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Con _ _) (force book -> Nil)) rT) -> do
      return term

    -- ctx |- n : R([])
    -- ctx |- c : ∀h:T. ∀t:T[]. R(h<>t)
    -- -------------------------------- LstM
    -- ctx |- λ{[]:n;<>:c} : ∀x:T[]. R
    (LstM n c, All (force book -> Lst a) rT) -> do
      n' <- check d span book ctx n (App rT Nil)
      c' <- check d span book ctx c $ All a (Lam "h" Nothing (\h -> All (Lst a) (Lam "t" Nothing (\t -> App rT (Con h t)))))
      return $ LstM n' c'

    -- Type mismatch for LstM
    (LstM n c, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Lst (Var "_" 0)) (Lam "_" Nothing (\_ -> (Var "?" 0))))) Nothing

    -- s ∈ tags
    -- ---------------------- Sym
    -- ctx |- &s : enum{tags}
    (Sym s, Enu y) -> do
      if s `elem` y
        then return term
        else Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Enu y)) (normal book (Sym s)) Nothing

    -- s ∈ tags, s == s1, s1 == s2
    -- -------------------------------- Sym-Eql
    -- ctx |- &s : enum{tags}{&s1==&s2}
    (Sym s, Eql (force book -> Enu syms) (force book -> Sym s1) (force book -> Sym s2)) -> do
      if s `elem` syms && s == s1 && s1 == s2
        then return term
        else Fail $ TermMismatch span (normalCtx book ctx) (normal book (Sym s1)) (normal book (Sym s2)) Nothing

    -- s1 == s2, (s1,t) ∈ cs => ctx |- t : R({==})
    -- s1 != s2 => ctx |- 
    -- ----------------------------------------------- EnuM-Eql
    -- ctx |- λ{cs;df} : ∀p:enum{syms}{&s1==&s2}. R(p)
    (EnuM cs df, All (force book -> Eql (force book -> Enu syms) (force book -> Sym s1) (force book -> Sym s2)) rT) -> do
      if s1 == s2
        then case lookup s1 cs of
          Just t -> do
            t' <- check d span book ctx t (App rT Rfl)
            return $ EnuM (map (\(s,t) -> if s == s1 then (s,t') else (s,t)) cs) df
          -- Nothing -> case df of
          --   Just df' -> check d span book ctx df' (All (Enu syms) (Lam "_" Nothing (\v -> App rT v)))
          --   Nothing  -> Fail $ IncompleteMatch span (normalCtx book ctx) Nothing -- TODO: CHECK THIS CLAUSE
          Nothing -> do
            df' <- check d span book ctx df (All (Enu syms) (Lam "_" Nothing (\v -> App rT v)))
            return $ EnuM cs df'
        else return term

    -- ∀(s,t) ∈ cs. ctx |- t : R(&s)
    -- not all_covered => ctx |- df : ∀x:enum{syms}. R(x)
    -- -------------------------------------------------- EnuM
    -- ctx |- λ{cs;df} : ∀x:enum{syms}. R
    (EnuM cs df, All (force book -> Enu syms) rT) -> do
      let covered_syms    = map fst cs
      let mismatched_syms = [s | s <- covered_syms, not (s `elem` syms)]
      case mismatched_syms of
        [] -> do
          let all_covered = length covered_syms >= length syms 
                         && all (`elem` syms) covered_syms
          cs' <- mapM (\(s, t) -> do t' <- check d span book ctx t (App rT (Sym s)); return (s,t')) cs
          if not all_covered
            then do
              let lam_goal = All (Enu syms) (Lam "_" Nothing (\v -> App rT v))
              df' <- check d span book ctx df lam_goal
              return $ EnuM cs' df'
            else return (EnuM cs' (Lam "_" Nothing (\_ -> One)))
        (h:t) -> do
          Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Enu [h, "..."]) (Lam "_" Nothing (\_ -> (Var "?" 0))))) Nothing

    -- Type mismatch for EnuM
    (EnuM cs df, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Enu []) (Lam "_" Nothing (\_ -> (Var "?" 0))))) Nothing

    -- ctx |- f : ∀xp:A{x1==x2}. ∀yp:B(x1){y1==y2}. R((xp,yp))
    -- ------------------------------------------------------- SigM-Eql
    -- ctx |- λ{(,):f} : ∀p:ΣA.B{(x1,y1)==(x2,y2)}. R(p)
    (SigM f, All (force book -> Eql (force book -> Sig a b) (force book -> Tup x1 y1) (force book -> Tup x2 y2)) rT) -> do
      f' <- check d span book ctx f (All (Eql a x1 x2) (Lam "xp" Nothing (\xp -> 
        All (Eql (App b x1) y1 y2) (Lam "yp" Nothing (\yp -> 
          App rT (Tup xp yp))))))
      return $ SigM f'

    -- ctx |- f : ∀x:A. ∀y:B(x). R((x,y))
    -- ----------------------------------- SigM
    -- ctx |- λ{(,):f} : ∀p:ΣA.B. R
    (SigM f, All (force book -> Sig a b) rT) -> do
      f' <- check d span book ctx f $ All a (Lam "x" Nothing (\h -> All (App b h) (Lam "y" Nothing (\t -> App rT (Tup h t)))))
      return $ SigM f'

    -- Type mismatch for SigM
    (SigM f, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Sig (Var "_" 0) (Lam "_" Nothing (\_ -> Var "_" 0))) (Lam "_" Nothing (\_ -> (Var "?" 0))))) Nothing

    -- ctx |- a : A
    -- ctx |- b : B(a)
    -- ------------------- Tup
    -- ctx |- (a,b) : ΣA.B
    (Tup a b, Sig aT bT) -> do
      a' <- check d span book ctx a aT
      b' <- check d span book ctx b (App bT a)
      return $ Tup a' b'

    -- ctx |- a : A{a1==a2}
    -- ctx |- b : B(a1){b1==b2}
    -- ------------------------------------- Tup-Eql
    -- ctx |- (a,b) : ΣA.B{(a1,b1)==(a2,b2)}
    (Tup a b, Eql (force book -> Sig aT bT) (force book -> Tup a1 b1) (force book -> Tup a2 b2)) -> do
      a' <- check d span book ctx a (Eql aT a1 a2)
      b' <- check d span book ctx b (Eql (App bT a1) b1 b2)
      return $ Tup a' b'

    -- equal a b
    -- --------------------- Rfl
    -- ctx |- {==} : T{a==b}
    (Rfl, Eql t a b) -> do
      if equal d book a b
        then return term
        else Fail $ TermMismatch span (normalCtx book ctx) (normal book a) (normal book b) Nothing

    -- ctx[a <- b] |- f : R({==})[a <- b]
    -- ----------------------------------- EqlM
    -- ctx |- λ{{==}:f} : ∀p:T{a==b}. R(p)
    (EqlM f, All (force book -> Eql t a b) rT) -> do
      let rewrittenGoal = rewrite d book a b (App rT Rfl)
      let rewrittenCtx  = rewriteCtx d book a b ctx
      f' <- check d span book rewrittenCtx f rewrittenGoal
      return $ EqlM f'

    -- ctx, k:T |- f : T
    -- ----------------- Fix
    -- ctx |- μk. f : T
    (Fix k f, _) -> do
      f' <- check (d+1) span book (extend ctx k (Fix k f) goal) (f (Fix k f)) goal
      return $ Fix k (\v -> bindVarByName k v f')

    -- ctx |- 
    -- -------------- Val-U64
    -- ctx |- n : U64
    (Val v@(U64_V _), Num U64_T) -> do
      return term

    -- ctx |- 
    -- -------------- Val-I64
    -- ctx |- n : I64
    (Val v@(I64_V _), Num I64_T) -> do
      return term

    -- ctx |- 
    -- -------------- Val-F64
    -- ctx |- n : F64
    (Val v@(F64_V _), Num F64_T) -> do
      return term

    -- ctx |- 
    -- --------------- Val-CHR
    -- ctx |- c : Char
    (Val v@(CHR_V _), Num CHR_T) -> do
      return term

    -- v1 == v2, v2 == v3
    -- --------------------- Val-Eql
    -- ctx |- v1 : T{v2==v3}
    (Val v1, Eql (force book -> Num t) (force book -> Val v2) (force book -> Val v3)) -> do
      if v1 == v2 && v2 == v3
        then return term
        else Fail $ TermMismatch span (normalCtx book ctx) (normal book (Val v2)) (normal book (Val v3)) Nothing

    -- ctx |- a : ta
    -- ctx |- b : tb
    -- inferOp2Type op ta tb = tr
    -- equal tr goal
    -- --------------------------- Op2
    -- ctx |- a op b : goal
    (Op2 op a b, _) -> do
      ta <- infer d span book ctx a Nothing
      tb <- infer d span book ctx b Nothing
      b' <- check d (getSpan span b) book ctx b ta
      tr <- inferOp2Type d span book ctx op ta tb
      if equal d book tr goal
        then return term
        else Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book tr) Nothing

    -- ctx |- a : ta
    -- inferOp1Type op ta = tr
    -- equal tr goal
    -- ----------------------- Op1
    -- ctx |- op a : goal
    (Op1 op a, _) -> do
      ta <- infer d span book ctx a Nothing
      tr <- inferOp1Type d span book ctx op ta
      if equal d book tr goal
        then return term
        else Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book tr) Nothing

    -- ctx |- a : T
    -- ctx |- b : T
    -- ------------------ Sup
    -- ctx |- &L{a,b} : T
    (Sup l a b, _) -> do
      a' <- check d span book ctx a goal
      b' <- check d span book ctx b goal
      return $ Sup l a' b'

    -- equal l l1, equal l1 l2
    -- ctx |- f : ∀ap:T{a1==a2}. ∀bp:T{b1==b2}. R(&l{ap,bp})
    -- ------------------------------------------------------ SupM-Eql
    -- ctx |- λ{&l{,}:f} : ∀p:T{&l1{a1,b1}==&l2{a2,b2}}. R(p)
    (SupM l f, All (force book -> Eql t (force book -> Sup l1 a1 b1) (force book -> Sup l2 a2 b2)) rT) -> do
      if equal d book l l1 && equal d book l1 l2
        then do
          f' <- check d span book ctx f (All (Eql t a1 a2) (Lam "ap" Nothing (\ap -> 
                 All (Eql t b1 b2) (Lam "bp" Nothing (\bp -> 
                   App rT (Sup l ap bp))))))
          return $ SupM l f'
        else Fail $ TermMismatch span (normalCtx book ctx) (normal book l1) (normal book l2) Nothing

    -- ctx |- l : U64
    -- ctx |- f : ∀p:T. ∀q:T. R(&l{p,q})
    -- --------------------------------- SupM
    -- ctx |- λ{&l{,}:f} : ∀x:T. R
    (SupM l f, _) -> do
      l' <- check d span book ctx l (Num U64_T)
      case force book goal of
        All xT rT -> do
          f' <- check d span book ctx f (All xT (Lam "p" Nothing (\p -> All xT (Lam "q" Nothing (\q -> App rT (Sup l p q))))))
          return $ SupM l' f'
        _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Var "_" 0) (Lam "_" Nothing (\_ -> (Var "?" 0))))) Nothing

    -- ctx |- l : U64
    -- ctx |- a : T
    -- ctx |- b : T
    -- -------------------------- Frk
    -- ctx |- fork l:a else:b : T
    (Frk l a b, _) -> do
      l' <- check d span book ctx l (Num U64_T)
      a' <- check d span book ctx a goal
      b' <- check d span book ctx b goal
      return $ Frk l' a' b'

    -- ctx |- e : T{a==b}
    -- ctx[a <- b] |- f : goal[a <- b]
    -- ------------------------------- Rwt
    -- ctx |- rewrite e f : goal
    (Rwt e f, _) -> do
      eT <- infer d span book ctx e Nothing
      eT <- infer d span book ctx e Nothing
      case force book eT of
        Eql t a b -> do
          let rewrittenCtx  = rewriteCtx d book a b ctx
          let rewrittenGoal = rewrite d book a b goal
          f' <- check d span book rewrittenCtx f rewrittenGoal
          -- e' <- check d span book ctx e eT
          -- check d span book rewrittenCtx f rewrittenGoal
          -- return $ Rwt e' f'
          return $ Rwt e f'
        _ ->
          Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0))) (normal book eT) Nothing

    -- Not supported
    (Pat _ _ _, _) -> do
      error "not-supported"

    -- ctx |- s : Char[]
    -- ctx |- x : T
    -- ------------------ Log
    -- ctx |- log s x : T
    (Log s x, _) -> do
      s' <- check d span book ctx s (Lst (Num CHR_T))
      x' <- check d span book ctx x goal
      return $ Log s' x'

    -- ctx |- x : T
    -- ------------------ HVM_INC
    -- ctx |- HVM_INC x : T
    (App (Pri HVM_INC) x, _) -> do
      x' <- check d span book ctx x goal
      return $ App (Pri HVM_INC) x'

    -- ctx |- x : T
    -- ------------------ HVM_DEC
    -- ctx |- HVM_DEC x : T
    (App (Pri HVM_DEC) x, _) -> do
      x' <- check d span book ctx x goal
      return $ App (Pri HVM_DEC) x'

    -- Type mismatch for Lam
    (Lam f t x, _) ->
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (Ref "Function" 1) Nothing

    -- ctx |- x : T
    -- ctx |- f : T -> T -> P
    -- ----------------------
    -- ctx |- (λ{&L:f} x) : P
    (App (SupM l f) x, _) -> do
      xT <- infer d span book ctx x Nothing
      x' <- check d span book ctx x xT
      f' <- check d span book ctx f (All xT (Lam "_" Nothing (\_ -> All xT (Lam "_" Nothing (\_ -> goal)))))
      l' <- check d span book ctx l (Num U64_T)
      return $ App (SupM l' f') x'

    (App fn@(Lam k mt b) x, _) -> do
      case mt of
        Just t ->  do
          t' <- check d span book ctx t Set
          x' <- check d span book ctx x t'
          check d span book ctx (b x') goal
        Nothing -> do
          check d span book ctx (b x) goal

    (App fn@(EqlM f) x@(cut -> Rfl), _) -> do
      let fn_name = "$aux_"++show d
      x'    <- check d span book ctx x (Eql Uni One One)
      goal' <- check d span book ctx goal Set
      check d span book ctx (Let fn_name (Just (All (Eql Uni One One) (Lam "_" Nothing (\_ -> goal')))) fn (\v -> App v x')) goal
    
    (App fn@(cut -> EmpM) x, _) -> do
      let fn_name = "$aux_"++show d
      x'    <- check d span book ctx x Emp
      goal' <- check d span book ctx goal Set
      check d span book ctx (Let fn_name (Just (All Emp (Lam "_" Nothing (\_ -> goal')))) fn (\v -> App v x')) goal
    
    (App fn@(cut -> UniM f) x, _) -> do
      let fn_name = "$aux_"++show d
      x'    <- check d span book ctx x Uni
      goal' <- check d span book ctx goal Set
      check d span book ctx (Let fn_name (Just (All Uni (Lam "_" Nothing (\_ -> goal')))) fn (\v -> App v x')) goal

    (App fn@(cut -> BitM f t) x, _) -> do
      let fn_name = "$aux_"++show d
      x'    <- check d span book ctx x Bit
      goal' <- check d span book ctx goal Set
      check d span book ctx (Let fn_name (Just (All Bit (Lam "_" Nothing (\_ -> goal')))) fn (\v -> App v x')) goal
    
    (App fn@(cut -> NatM z s) x, _) -> do
      let fn_name = "$aux_"++show d
      x'    <- check d span book ctx x Nat
      goal' <- check d span book ctx goal Set
      check d span book ctx (Let fn_name (Just (All Nat (Lam "_" Nothing (\_ -> goal')))) fn (\v -> App v x')) goal
    
    (App fn@(cut -> LstM n c) x@(cut -> Nil), _) -> do
      check d span book ctx n goal
    (App fn@(cut -> LstM n c) x, _) -> do
      let fn_name = "$aux_"++show d
      xT <- infer d span book ctx x Nothing
      case cut $ force book xT of
        Lst hT -> do
          x'    <- check d span book ctx x xT
          goal' <- check d span book ctx goal Set
          check d span book ctx (Let fn_name (Just (All (Lst hT) (Lam "_" Nothing (\_ -> goal')))) fn (\v -> App v x')) goal
        _      -> do
          Fail $ TypeMismatch span (normalCtx book ctx) (All (Var "_" 0) (Lam "_" Nothing (\_ -> (Var "_" 0)))) (normal book xT) Nothing
    
    (App fn@(cut -> SigM g) x, _) ->
      do
      let fn_name = "$aux_"++show d
      xT' <- infer d span book ctx x (Just term)
      xT  <- derefADT <$> check d span book ctx xT' Set

      case cut $ force book xT of
        Sig _ _ -> do
          x' <- check d span book ctx x xT
          goal' <- check d span book ctx goal Set
          check d span book ctx (Let fn_name (Just (All xT (Lam "_" Nothing (\_ -> goal')))) fn (\v -> App v x')) goal
        _       -> do
          Fail $ TypeMismatch (getSpan span x) (normalCtx book ctx) (Var "Σ_:_._" 0) (normal book xT) Nothing
        where
          derefADT trm = case cut trm of
            Ref k i ->
              let xTbody = getDefn book k in
              case xTbody of
                Just (_, cut -> bod@(Sig (cut -> Enu _) _), _) -> bod
                _ -> trm
            _ -> trm

    -- (App fn@(cut -> SigM g) x, _) -> do
    --   xT <- case cut x of
    --     Tup a b -> do
    --       inferIndirect d span book ctx x term
    --     _ -> do
    --       xTinfer <- infer d span book ctx x
    --       Done $ derefADT xTinfer
    --         where
    --           derefADT trm = case cut trm of
    --             Ref k i ->
    --               let xTbody = getDefn book k in
    --               case xTbody of
    --                 Just (_, cut -> bod@(Sig (cut -> Enu _) _), _) -> bod
    --                 _ -> trm
    --             _ -> trm
    --
    --   -- traceM $ "- INFERRED: " ++ show x ++ " :: " ++ show xT
    --   x' <- check d span book ctx x xT
    --   case cut $ normal book xT of
    --     Sig aT bTFunc@(cut -> Lam y mty yb) -> do
    --       case cut g of
    --         Lam l mtl lb -> do
    --           case cut (lb (Var l d)) of
    --             Lam r mtr rb -> do
    --               let lV = case cut x of
    --                       Tup a b -> a
    --                       _       -> Var l d
    --               let rV = case cut x of
    --                       Tup a b -> b
    --                       _       -> Var r (d+1)
    --               let tupV = Tup lV rV
    --               let bT = App bTFunc lV 
    --               let ctxWithPair = extend (extend ctx l lV aT) r rV bT
    --               let ctxRewritten  = rewriteCtx (d+2) book x tupV ctxWithPair
    --               let bodyRewritten = rewrite    (d+2) book x tupV $ rewrite (d+2) book (Var l d) lV (rb rV)
    --               let goalRewritten = rewrite    (d+2) book x tupV goal
    --               g' <- (\v -> Lam l mtl (\lv -> (Lam r mtr (\rv -> bindVarByNameMany ([(l,lv),(r,rv)]) v)))) 
    --                 <$> check (d+2) span book ctxRewritten bodyRewritten goalRewritten
    --               let fnType = All xT (SigM (Lam l mtl (\lv -> (Lam r mtr (\rv -> bindVarByNameMany [(l,lv),(r,rv)] goalRewritten)))))
    --               case cut x of
    --                 Var{} -> return $ App (reWrap fn $ SigM g') x'
    --                 _     -> return $ App (Chk (reWrap fn $ SigM g') fnType) x'
    --             _ -> do
    --               let bT = App bTFunc (Var l d)
    --               check d span book ctx g (All aT (Lam l Nothing (\_ -> All bT (Lam "_" Nothing (\_ -> goal)))))
    --         _ -> do
    --           verify d span book ctx term goal
    --     _ -> do
    --       verify d span book ctx term goal
    --
    -- (App (cut -> EnuM cs df) x, _) -> do
    --   xT <- infer d span book ctx x
    --   let doT = case cs of
    --         []          -> Nothing
    --         ((s,t):_)   -> case infer d span book ctx (Sym s) of
    --           Done doT' -> Just doT'
    --           _         -> Nothing
    --   case (cut xT, doT) of
    --     (Enu syms, Just (Enu syms')) | syms == syms' -> do
    --           cs' <- mapM (\(s, t) -> do
    --             ty <- check d span book (rewriteCtx d book x (Sym s) ctx) t (rewrite d book x (Sym s) goal)
    --             return (s, ty)
    --             ) cs
    --           return $ App (EnuM cs' df) x
    --     _ -> do
    --       verify d span book ctx term goal

    -- Default case: try to infer and verify
    (term, _) -> 
      do 
      let (fn, xs) = collectApps term []
      if isLam fn then do
        -- verify d span book ctx term goal
        Fail $ Unsupported span (normalCtx book ctx) (Just $ show term)
      else do
        verify d span book ctx term goal

-- Verify that a term has the expected type by inference
verify :: Int -> Span -> Book -> Ctx -> Term -> Term -> Result Term
verify d span book ctx term goal = do
  t <- infer d span book ctx term Nothing
  if
    trace ("-verify: " ++ show term ++ " :: " ++ show t ++ " == " ++ show goal) $
    equal d book t goal
    then do 
      return term
    else 
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book t) Nothing

