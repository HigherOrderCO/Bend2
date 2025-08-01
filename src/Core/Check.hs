{-./Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Check where

import qualified Data.Map as M
import Data.List (find)

import Debug.Trace

import Core.Equal
import Core.Rewrite
import Core.Type
import Core.WHNF

-- Context
-- -------

extend :: Ctx -> Name -> Term -> Term -> Ctx
extend (Ctx ctx) k v t = Ctx (ctx ++ [(k, v, t)])

format :: Int -> Book -> Term -> Term
format d book x = normal d book $ x
-- format d book x = x

formatCtx :: Int -> Book -> Ctx -> Ctx
formatCtx d book (Ctx ctx) = Ctx (map formatAnn ctx)
  where formatAnn (k,v,t) = (k, format d book v, format d book t)

-- Type Checker
-- ------------

-- Infer the type of a term
infer :: Int -> Span -> Book -> Ctx -> Term -> Result Term
infer d span book@(Book defs) ctx term =
  -- trace ("- infer: " ++ show (format d book term)) $
  case term of
    Var _ i -> do
      let Ctx ks = ctx
      if i < length ks
        then let (_, _, typ) = ks !! i
             in Done typ
        else Fail $ CantInfer span (formatCtx d book ctx)
    Ref k -> do
      case deref book k of
        Just (_, _, typ) -> Done typ
        Nothing          -> Fail $ Undefined span (formatCtx d book ctx) k
    Sub x -> do
      infer d span book ctx x
    Let k t v f -> case t of
      Just t  -> do
        check d span book ctx v t
        infer (d+1) span book (extend ctx k v t) (f v)
      Nothing -> do
        t <- infer d span book ctx v
        infer (d+1) span book (extend ctx k v t) (f v)
    Fix k f -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    Chk v t -> do
      check d span book ctx v t
      Done t
    Set -> do
      Done Set
    Emp -> do
      Done Set
    EmpM _ -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    Uni -> do
      Done Set
    One -> do
      Done Uni
    UniM _ _ -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    Bit -> do
      Done Set
    Bt0 -> do
      Done Bit
    Bt1 -> do
      Done Bit
    BitM _ _ _ -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    Nat -> do
      Done Set
    Zer -> do
      Done Nat
    Suc n -> do
      nT <- infer d span book ctx n
      case force book nT of
        Nat ->
          Done $ Nat
        Eql Nat a b ->
          Done $ Eql Nat (Suc a) (Suc b)
        _ ->
          Fail $ TypeMismatch span (formatCtx d book ctx) (format d book Nat) (format d book nT)
    NatM _ _ _ -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    Lst t -> do
      check d span book ctx t Set
      Done Set
    Nil -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    Con h t -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    LstM _ _ _ -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    Enu s -> do
      Done Set
    Sym s -> do
      let bookEnums = [ Enu tags | (k, (_, (Sig (Enu tags) _), Set)) <- M.toList defs ]
      case find isEnuWithTag bookEnums of
        Just t  -> Done t
        Nothing -> Fail $ CantInfer span (formatCtx d book ctx)
        where
          isEnuWithTag (Enu tags) = s `elem` tags
          isEnuWithTag _ = False
    EnuM _ _ _ -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    Sig a b -> do
      check d span book ctx a Set
      check d span book ctx b (All a (Lam "_" Nothing (\_ -> Set)))
      Done Set
    Tup a b -> do
      aT <- infer d span book ctx a
      bT <- infer d span book ctx b
      Done $ Sig aT (Lam "_" Nothing (\_ -> bT))
    SigM _ _ -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    All a b -> do
      check d span book ctx a Set
      check d span book ctx b (All a (Lam "_" Nothing (\_ -> Set)))
      Done Set
    Lam k t b -> case t of
      Just tk  -> do 
        let x = Var k d
        tb <- infer (d+1) span book (extend ctx k x tk) (b x)
        Done $ All tk (Lam k (Just tk) (\v -> tb))
      Nothing -> do
        Fail $ CantInfer span (formatCtx d book ctx)
    App f x ->
      case f of
        Lam k t body -> do
          xT <- infer d span book ctx x
          infer (d+1) span book (extend ctx k x xT) (body x)
        _ -> do
          fT <- infer d span book ctx f
          case force book fT of
            All fA fB -> do
              check d span book ctx x fA
              Done $ App fB x
            _ -> do
              Fail $ TypeMismatch span (formatCtx d book ctx) (format d book (All (Var "_" 0) (Lam "_" Nothing (\_ -> Var "_" 0)))) (format d book fT)
    Eql t a b -> do
      check d span book ctx t Set
      check d span book ctx a t
      check d span book ctx b t
      Done Set
    Rfl -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    EqlM _ _ -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    Ind _ -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    Frz _ -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    Loc l t ->
      infer d l book ctx t
    Rwt a b x ->
      Fail $ CantInfer span (formatCtx d book ctx)
    Era -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    Sup l a b -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    SupM x l f -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    Frk l a b -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    Met _ _ _ -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    Num _ -> do
      Done Set
    Val (U64_V _) -> do
      Done (Num U64_T)
    Val (I64_V _) -> do
      Done (Num I64_T)
    Val (F64_V _) -> do
      Done (Num F64_T)
    Val (CHR_V _) -> do
      Done (Num CHR_T)
    Op2 op a b -> do
      ta <- infer d span book ctx a
      tb <- infer d span book ctx b
      inferOp2Type d span book ctx op a b ta tb
    Op1 op a -> do
      ta <- infer d span book ctx a
      inferOp1Type d span book ctx op a ta
    Pri U64_TO_CHAR -> do
      Done (All (Num U64_T) (Lam "x" Nothing (\_ -> Num CHR_T)))
    Pri CHAR_TO_U64 -> do
      Done (All (Num CHR_T) (Lam "x" Nothing (\_ -> Num U64_T)))
    Pri HVM_INC -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    Pri HVM_DEC -> do
      Fail $ CantInfer span (formatCtx d book ctx)
    Log s x -> do
      check d span book ctx s (Lst (Num CHR_T))
      infer d span book ctx x
    Pat _ _ _ -> do
      error "Pat not supported in infer"

-- Infer the result type of a binary numeric operation
inferOp2Type :: Int -> Span -> Book -> Ctx -> NOp2 -> Term -> Term -> Term -> Term -> Result Term
inferOp2Type d span book ctx op a b ta tb = do
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
      (Num t1, Num t2) | t1 == t2 -> Done (Num t1)
      (Nat, Nat) -> Done Nat  -- Allow Nat arithmetic operations
      _ -> Fail $ TypeMismatch span (formatCtx d book ctx) (format d book (Ref "Num")) (format d book ta)
    
    comparisonOp ta tb = case (force book ta, force book tb) of
      (Num t1, Num t2) | t1 == t2 -> Done Bit
      (Bit, Bit) -> Done Bit  -- Allow Bool comparison
      (Nat, Nat) -> Done Bit  -- Allow Nat comparison
      _ -> Fail $ TypeMismatch span (formatCtx d book ctx) (format d book ta) (format d book tb)
    
    integerOp ta tb = case (force book ta, force book tb) of
      (Num U64_T, Num U64_T) -> Done (Num U64_T)
      (Num I64_T, Num I64_T) -> Done (Num U64_T)  -- Bitwise on I64 returns U64
      (Num F64_T, Num F64_T) -> Done (Num U64_T)  -- Bitwise on F64 returns U64
      (Num CHR_T, Num CHR_T) -> Fail $ TypeMismatch span (formatCtx d book ctx) (format d book (Ref "Num")) (format d book ta)  -- Bitwise not supported for CHR
      _ -> Fail $ TypeMismatch span (formatCtx d book ctx) (format d book (Ref "Num")) (format d book ta)
    
    boolOrIntegerOp ta tb = case (force book ta, force book tb) of
      (Bit, Bit) -> Done Bit  -- Logical operations on booleans
      (Num U64_T, Num U64_T) -> Done (Num U64_T)  -- Bitwise operations on integers
      (Num I64_T, Num I64_T) -> Done (Num U64_T)
      (Num F64_T, Num F64_T) -> Done (Num U64_T)
      _ -> Fail $ TypeMismatch span (formatCtx d book ctx) (format d book ta) (format d book tb)

-- Infer the result type of a unary numeric operation
inferOp1Type :: Int -> Span -> Book -> Ctx -> NOp1 -> Term -> Term -> Result Term
inferOp1Type d span book ctx op a ta = case op of
  NOT -> case force book ta of
    Bit       -> Done Bit  -- Logical NOT on Bool
    Num U64_T -> Done (Num U64_T)
    Num I64_T -> Done (Num U64_T)  -- Bitwise NOT on I64 returns U64
    Num F64_T -> Done (Num U64_T)  -- Bitwise NOT on F64 returns U64
    Num CHR_T -> Fail $ CantInfer span (formatCtx d book ctx)  -- Bitwise NOT not supported for CHR
    _         -> Fail $ CantInfer span (formatCtx d book ctx)
  NEG -> case force book ta of
    Num I64_T -> Done (Num I64_T)
    Num F64_T -> Done (Num F64_T)
    Num CHR_T -> Fail $ CantInfer span (formatCtx d book ctx)  -- Negation not supported for CHR
    _         -> Fail $ CantInfer span (formatCtx d book ctx)

-- Check if a term has the expected type
check :: Int -> Span -> Book -> Ctx -> Term -> Term -> Result ()
check d span book ctx term goal =
  -- trace ("- check: " ++ show (format d book term) ++ " :: " ++ show (format d book goal)) $
  case (term, force book goal) of
    (term, Rwt a b goal) -> do
      let new_ctx  = rewriteCtx 3 d book a b ctx
      let new_goal = rewrite 3 d book a b goal
      let new_term = rewrite 0 d book a b term
      -- trace ("> REWRITE " ++ show (normal d book a) ++ " → " ++ show (normal d book b) ++ ":\n" ++
        -- "- ctx : " ++ show (normalCtx d book ctx) ++ " → " ++ show (normalCtx d book new_ctx) ++ "\n" ++
        -- "- goal: " ++ show (normal d book goal) ++ " → " ++ show (normal d book new_goal)) $
      check d span book new_ctx new_term new_goal
    (Era, _) -> do
      Done ()
    (Let k t v f, _) -> case t of
        Just t  -> do
          check d span book ctx v t
          check (d+1) span book (extend ctx k v t) (f v) goal
        Nothing -> do
          t <- infer d span book ctx v
          check (d+1) span book (extend ctx k v t) (f v) goal
    (One, Uni) -> do
      Done ()
    (Bt0, Bit) -> do
      Done ()
    (Bt1, Bit) -> do
      Done ()
    (Zer, Nat) -> do
      Done ()
    (Suc n, Eql t (force book -> Suc a) (force book -> Suc b)) -> do
      check d span book ctx n (Eql t a b)
    (Suc n, Nat) -> do
      check d span book ctx n Nat
    (Nil, Lst _) -> do
      Done ()
    (Nil, goal) ->
      Fail $ TypeMismatch span (formatCtx d book ctx) (format d book (Lst (Var "_" 0))) (format d book goal)
    (Con h t, Lst tT) -> do
      check d span book ctx h tT
      check d span book ctx t (Lst tT)
    (Lam k t f, All a (Lam _ _ b)) -> do
      let x = Var k d
      check (d+1) span book (extend ctx k x a) (f x) (b x)
    (EmpM x, _) -> do
      xT <- infer d span book ctx x
      case force book xT of
        Emp -> do
          Done ()
        Eql t a b -> do
          check d span book ctx a t
          check d span book ctx b t
          if not (equal d book a b)
            then Done ()
            else Fail $ TermMismatch span (formatCtx d book ctx) (format d book a) (format d book b)
        _ -> Fail $ TypeMismatch span (formatCtx d book ctx) (format d book Emp) (format d book xT)
    (UniM x f, _) -> do
      xT <- infer d span book ctx x
      case force book xT of
        Uni -> do
          check d span book ctx f (Rwt x One goal)
        _ -> Fail $ TypeMismatch span (formatCtx d book ctx) (format d book Uni) (format d book xT)
    (BitM x f t, _) -> do
      xT <- infer d span book ctx x
      case force book xT of
        Bit -> do
          check d span book ctx f (Rwt x Bt0 goal)
          check d span book ctx t (Rwt x Bt1 goal)
        _ -> Fail $ TypeMismatch span (formatCtx d book ctx) (format d book Bit) (format d book xT)
    (NatM x z s, _) -> do
      xT <- infer d span book ctx x
      case force book xT of
        Nat -> do
          check d span book ctx z (Rwt x Zer goal)
          check d span book ctx s $ All Nat (Lam "p" Nothing (\p -> Rwt x (Suc p) goal))
        _ -> Fail $ TypeMismatch span (formatCtx d book ctx) (format d book Nat) (format d book xT)
    (LstM x n c, _) -> do
      xT <- infer d span book ctx x
      case force book xT of
        Lst a -> do
          check d span book ctx n (Rwt x Nil goal)
          check d span book ctx c $ All a (Lam "h" Nothing (\h -> All (Lst a) (Lam "t" Nothing (\t -> Rwt x (Con h t) goal))))
        _ -> Fail $ TypeMismatch span (formatCtx d book ctx) (format d book (Lst (Var "_" 0))) (format d book xT)
    (Sym s, Enu y) -> do
      if s `elem` y
        then Done ()
        else Fail $ TypeMismatch span (formatCtx d book ctx) (format d book (Enu y)) (format d book (Sym s))
    (EnuM x cs df, _) -> do
      xT <- infer d span book ctx x
      case force book xT of
        Enu syms -> do
          mapM_ (\(s, t) -> check d span book ctx t (Rwt x (Sym s) goal)) cs
          let covered_syms = map fst cs
          let all_covered = length covered_syms >= length syms
                         && all (`elem` syms) covered_syms
          if not all_covered
            then do
              case df of
                (cut -> Lam k Nothing (unlam k d -> One)) -> do
                  Fail $ IncompleteMatch span (formatCtx d book ctx)
                otherwise -> do
                  let enu_type = Enu syms
                  let lam_goal = All enu_type (Lam "_" Nothing (\v -> Rwt x v goal))
                  check d span book ctx df lam_goal
            else Done ()
        _ -> Fail $ TypeMismatch span (formatCtx d book ctx) (format d book (Enu [])) (format d book xT)
    (SigM x f, _) -> do
      xT <- infer d span book ctx x
      case force book xT of
        Sig a b -> do
          check d span book ctx f $ All a (Lam "x" Nothing (\h -> All (App b h) (Lam "y" Nothing (\t -> Rwt x (Tup h t) goal))))
        _ -> Fail $ TypeMismatch span (formatCtx d book ctx) (format d book (Sig (Var "_" 0) (Lam "_" Nothing (\_ -> Var "_" 0)))) (format d book xT)
    (Tup a b, Sig aT (Lam _ _ bT)) -> do
      check d span book ctx a aT
      check d span book ctx b (bT a)
    (Rfl, Eql t a b) -> do
      check d span book ctx a t
      check d span book ctx b t
      if equal d book a b
        then Done ()
        else Fail $ TermMismatch span (formatCtx d book ctx) (format d book a) (format d book b)
    (EqlM x f, _) -> do
      xT <- infer d span book ctx x
      case force book xT of
        Eql t a b -> do
          check d span book ctx f (Rwt x Rfl (Rwt a b goal))
        _ -> Fail $ TypeMismatch span (formatCtx d book ctx) (format d book (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0))) (format d book xT)
    (Fix k f, _) -> do
      check (d+1) span book (extend ctx k (Fix k f) goal) (f (Fix k f)) goal
    (Loc l t, _) -> do
      check d l book ctx t goal
    (Val (U64_V _), Num U64_T) -> do
      Done ()
    (Val (I64_V _), Num I64_T) -> do
      Done ()
    (Val (F64_V _), Num F64_T) -> do
      Done ()
    (Val (CHR_V _), Num CHR_T) -> do
      Done ()
    (Op2 op a b, _) -> do
      ta <- infer d span book ctx a
      tb <- infer d span book ctx b
      tr <- inferOp2Type d span book ctx op a b ta tb
      if equal d book tr goal
        then Done ()
        else Fail $ TypeMismatch span (formatCtx d book ctx) (format d book goal) (format d book tr)
    (Op1 op a, _) -> do
      ta <- infer d span book ctx a
      tr <- inferOp1Type d span book ctx op a ta
      if equal d book tr goal
        then Done ()
        else Fail $ TypeMismatch span (formatCtx d book ctx) (format d book goal) (format d book tr)
    (Sup l a b, _) -> do
      check d span book ctx a goal
      check d span book ctx b goal
    (SupM x l f, _) -> do
      check d span book ctx l (Num U64_T)
      xT <- infer d span book ctx x
      check d span book ctx f (All xT (Lam "p" Nothing (\p -> All xT (Lam "q" Nothing (\q -> Rwt x (Sup l p q) goal)))))
    (Frk l a b, _) -> do
      check d span book ctx l (Num U64_T)
      check d span book ctx a goal
      check d span book ctx b goal
    (Pat _ _ _, _) -> do
      error "not-supported"
    (App (Pri HVM_INC) x, _) ->
      check d span book ctx x goal
    (App (Pri HVM_DEC) x, _) ->
      check d span book ctx x goal
    -- (f x) :: G
    -- --------------------------------------------------- specialize
    -- f :: ∀(v : typeof x). (G where x is rewritten by v)
    (App f x, _) ->
      if isLamApp f
        then do
          xt <- infer d span book ctx x
          check d span book ctx f $ All xt $ Lam "_" Nothing $ \v -> Rwt x v goal
        else do
          verify d span book ctx term goal
    (Log s x, _) -> do
      check d span book ctx s (Lst (Num CHR_T))
      check d span book ctx x goal
    (Lam f t x, _) ->
      Fail $ TypeMismatch span (formatCtx d book ctx) (format d book goal) (Ref "Function")
    (_, _) -> do
      verify d span book ctx term goal

-- Verify that a term has the expected type by inference
verify :: Int -> Span -> Book -> Ctx -> Term -> Term -> Result ()
verify d span book ctx term goal = do
  t <- infer d span book ctx term
  if equal d book t goal
    then Done ()
    else Fail $ TypeMismatch span (formatCtx d book ctx) (format d book goal) (format d book t)

-- Utils
-- -----

-- Check all definitions in a Book
checkBook :: Book -> Result ()
checkBook book@(Book defs) = mapM_ checkDef (M.toList defs)
  where
    checkDef (name, (_, term, typ)) = do
      check 0 noSpan book (Ctx []) term typ

-- Utils
-- -----

isLamApp :: Term -> Bool
isLamApp (cut -> App f _)    = isLamApp f
isLamApp (cut -> Lam _ _ _)    = True
isLamApp (cut -> EmpM _)     = True
isLamApp (cut -> UniM _ _)   = True
isLamApp (cut -> BitM _ _ _) = True
isLamApp (cut -> NatM _ _ _) = True
isLamApp (cut -> LstM _ _ _) = True
isLamApp (cut -> EnuM _ _ _) = True
isLamApp (cut -> SigM _ _)   = True
isLamApp (cut -> EqlM _ _)   = True
isLamApp _                   = False
