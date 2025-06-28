{-./Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Check where

import qualified Data.Map as M

import Debug.Trace

import Core.Type
import Core.WHNF

-- Context
-- -------

extend :: Ctx -> Name -> Term -> Term -> Ctx
extend (Ctx ctx) k v t = Ctx (ctx ++ [(k, v, t)])

-- Type Checker
-- ------------

-- Infer the type of a term
infer :: Int -> Span -> Book -> Subs -> Ctx -> Term -> Result Term
infer d span book subs ctx term =
  -- trace ("- infer: " ++ show (normal 3 d book subs term)) $
  case term of
    Var k i -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    Ref k -> do
      case deref book k of
        Just (_, _, typ) -> Done typ
        Nothing          -> Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    Sub x -> do
      infer d span book subs ctx x
    Let v f -> do
      case v of
        Chk val typ -> do
          check d span book subs ctx val typ
          infer d span book subs ctx (App f (Ann val typ))
        _ -> do
          t <- infer d span book subs ctx v
          infer d span book subs ctx (App f (Ann v t))
    Fix k f -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    Ann v t -> do
      Done t
    Chk v t -> do
      check d span book subs ctx v t
      Done t
    Set -> do
      Done Set
    Emp -> do
      Done Set
    Efq -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    Uni -> do
      Done Set
    One -> do
      Done Uni
    UniM _ _ -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    Bit -> do
      Done Set
    Bt0 -> do
      Done Bit
    Bt1 -> do
      Done Bit
    BitM _ _ _ -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    Nat -> do
      Done Set
    Zer -> do
      Done Nat
    Suc n -> do
      nT <- infer d span book subs ctx n
      case force d book subs nT of
        Nat ->
          Done $ Nat
        Eql Nat a b ->
          Done $ Eql Nat (Suc a) (Suc b)
        _ ->
          Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs Nat) (normal 3 d book subs nT)
    NatM _ _ _ -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    Lst t -> do
      check d span book subs ctx t Set
      Done Set
    Nil -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    Con h t -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    LstM _ _ _ -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    Enu s -> do
      Done Set
    Sym s -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    EnuM _ _ _ -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    Sig a b -> do
      check d span book subs ctx a Set
      check d span book subs ctx b (All a (Lam "_" (\_ -> Set)))
      Done Set
    Tup a b -> do
      aT <- infer d span book subs ctx a
      bT <- infer d span book subs ctx b
      Done $ Sig aT (Lam "_" (\_ -> bT))
    SigM _ _ -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    All a b -> do
      check d span book subs ctx a Set
      check d span book subs ctx b (All a (Lam "_" (\_ -> Set)))
      Done Set
    Lam _ _ -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    App f x ->
      case (f,x) of
        -- TODO: can we generalize this to other lam forms?
        (Lam k f, Ann xv xt) -> do
          infer (d+1) span book subs (extend ctx k xv xt) (f (Ann xv xt))
        _ -> do
          fT <- infer d span book subs ctx f
          case force d book subs fT of
            All fA fB -> do
              check d span book subs ctx x fA
              Done $ App fB x
            _ -> do
              Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs (All (Var "_" 0) (Lam "_" (\_ -> Var "_" 0)))) (normal 3 d book subs fT)
    Eql t a b -> do
      Done Set
    Rfl -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    EqlM _ _ -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    Ind _ -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    Frz _ -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    Loc l t ->
      infer d l book subs ctx t
    Rwt a b x ->
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    Era -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    Sup l a b -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
    Met _ _ _ -> do
      Fail $ CantInfer span (normalCtx 3 d book subs ctx)
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
      ta <- infer d span book subs ctx a
      tb <- infer d span book subs ctx b
      inferOp2Type d span book subs ctx op a b ta tb
    Op1 op a -> do
      ta <- infer d span book subs ctx a
      inferOp1Type d span book subs ctx op a ta
    Pri U64_TO_CHAR -> do
      Done (All (Num U64_T) (Lam "x" (\_ -> Num CHR_T)))
    Pat _ _ _ -> do
      error "Pat not supported in infer"

-- Infer the result type of a binary numeric operation
inferOp2Type :: Int -> Span -> Book -> Subs -> Ctx -> NOp2 -> Term -> Term -> Term -> Term -> Result Term
inferOp2Type d span book subs ctx op a b ta tb = do
  -- For arithmetic ops, both operands must have the same numeric type
  case op of
    ADD -> numericOp ta tb
    SUB -> numericOp ta tb
    MUL -> numericOp ta tb
    DIV -> numericOp ta tb
    MOD -> numericOp ta tb
    -- Comparison ops return Bool
    EQL -> comparisonOp ta tb
    NEQ -> comparisonOp ta tb
    LST -> comparisonOp ta tb
    GRT -> comparisonOp ta tb
    LEQ -> comparisonOp ta tb
    GEQ -> comparisonOp ta tb
    -- Bitwise ops require integer types
    AND -> integerOp ta tb
    OR  -> integerOp ta tb
    XOR -> integerOp ta tb
    SHL -> integerOp ta tb
    SHR -> integerOp ta tb
  where
    numericOp ta tb = case (force d book subs ta, force d book subs tb) of
      (Num t1, Num t2) | t1 == t2 -> Done (Num t1)
      _ -> Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs ta) (normal 3 d book subs tb)
    
    comparisonOp ta tb = case (force d book subs ta, force d book subs tb) of
      (Num t1, Num t2) | t1 == t2 -> Done Bit
      _ -> Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs ta) (normal 3 d book subs tb)
    
    integerOp ta tb = case (force d book subs ta, force d book subs tb) of
      (Num U64_T, Num U64_T) -> Done (Num U64_T)
      (Num I64_T, Num I64_T) -> Done (Num U64_T)  -- Bitwise on I64 returns U64
      (Num F64_T, Num F64_T) -> Done (Num U64_T)  -- Bitwise on F64 returns U64
      (Num CHR_T, Num CHR_T) -> Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs ta) (normal 3 d book subs tb)  -- Bitwise not supported for CHR
      _ -> Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs ta) (normal 3 d book subs tb)

-- Infer the result type of a unary numeric operation
inferOp1Type :: Int -> Span -> Book -> Subs -> Ctx -> NOp1 -> Term -> Term -> Result Term
inferOp1Type d span book subs ctx op a ta = case op of
  NOT -> case force d book subs ta of
    Num U64_T -> Done (Num U64_T)
    Num I64_T -> Done (Num U64_T)  -- Bitwise NOT on I64 returns U64
    Num F64_T -> Done (Num U64_T)  -- Bitwise NOT on F64 returns U64
    Num CHR_T -> Fail $ CantInfer span (normalCtx 3 d book subs ctx)  -- Bitwise NOT not supported for CHR
    _         -> Fail $ CantInfer span (normalCtx 3 d book subs ctx)
  NEG -> case force d book subs ta of
    Num I64_T -> Done (Num I64_T)
    Num F64_T -> Done (Num F64_T)
    Num CHR_T -> Fail $ CantInfer span (normalCtx 3 d book subs ctx)  -- Negation not supported for CHR
    _         -> Fail $ CantInfer span (normalCtx 3 d book subs ctx)

-- Check if a term has the expected type
check :: Int -> Span -> Book -> Subs -> Ctx -> Term -> Term -> Result ()
check d span book subs ctx term goal =
  -- trace ("- check: " ++ show (normal 3 d book subs term) ++ " :: " ++ show (normal 3 d book subs goal)) $
  case (term, force d book subs goal) of
    (term, Rwt a b goal) -> do
      -- trace ("oxi " ++ show a ++ " → " ++ show b ++ " :: " ++ show goal) $
      check d span book (subs++[(a,b)]) ctx term goal
    (Let v f, _) -> do
      case v of
        Chk val typ -> do
          check d span book subs ctx val typ
          check d span book subs ctx (App f (Ann val typ)) goal
        _ -> do
          t <- infer d span book subs ctx v
          check d span book subs ctx (App f (Ann v t)) goal
    (One, Uni) -> do
      Done ()
    (Bt0, Bit) -> do
      Done ()
    (Bt1, Bit) -> do
      Done ()
    (Zer, Nat) -> do
      Done ()
    (Suc n, Eql t (force d book subs -> Suc a) (force d book subs -> Suc b)) -> do
      check d span book subs ctx n (Eql t a b)
    (Suc n, Nat) -> do
      check d span book subs ctx n Nat
    (Nil, Lst _) -> do
      Done ()
    (Nil, goal) ->
      Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs (Lst (Var "_" 0))) (normal 3 d book subs goal)
    (Con h t, Lst tT) -> do
      check d span book subs ctx h tT
      check d span book subs ctx t (Lst tT)
    -- FIXME: doesn't work if we use 'All a b' because whnf removes the Ann (same for Sig)
    (Lam k f, All a (Lam _ b)) -> do
      let x = Ann (Var k d) a
      check (d+1) span book subs (extend ctx k (Var k d) a) (f x) (b x)
    (Efq, All a _) -> do
      case force d book subs a of
        Emp -> Done ()
        _ -> Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs Emp) (normal 3 d book subs a)
    (UniM x f, goal) -> do
      xT <- infer d span book subs ctx x
      case force d book subs xT of
        Uni -> do
          check d span book subs ctx f (Rwt x One goal)
        _ -> Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs Uni) (normal 3 d book subs xT)
    (BitM x f t, goal) -> do
      xT <- infer d span book subs ctx x
      case force d book subs xT of
        Bit -> do
          check d span book subs ctx f (Rwt x Bt0 goal)
          check d span book subs ctx t (Rwt x Bt1 goal)
        _ -> Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs Bit) (normal 3 d book subs xT)
    (NatM x z s, goal) -> do
      xT <- infer d span book subs ctx x
      case force d book subs xT of
        Nat -> do
          check d span book subs ctx z (Rwt x Zer goal)
          -- check d span book ((x,Suc (Var "p" d)):subs) ctx s $ All Nat (Lam "p" (\p -> goal))
          check d span book subs ctx s $ All Nat (Lam "p" (\p -> Rwt x (Suc p) goal))
        _ -> Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs Nat) (normal 3 d book subs xT)
    (LstM x n c, goal) -> do
      xT <- infer d span book subs ctx x
      case force d book subs xT of
        Lst a -> do
          check d span book subs ctx n (Rwt x Nil goal)
          -- check d span book ((x,Con (Var "h" d) (Var "t" (d+1))):subs) ctx c $ All a (Lam "h" (\h -> All (Lst a) (Lam "t" (\t -> goal))))
          check d span book subs ctx c $ All a (Lam "h" (\h -> All (Lst a) (Lam "t" (\t -> Rwt x (Con h t) goal))))
        _ -> Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs (Lst (Var "_" 0))) (normal 3 d book subs xT)
    (Sym s, Enu y) -> do
      if s `elem` y
        then Done ()
        else Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs (Enu y)) (normal 3 d book subs (Sym s))
    (EnuM x cs df, goal) -> do
      xT <- infer d span book subs ctx x
      case force d book subs xT of
        Enu syms -> do
          mapM_ (\(s, t) -> check d span book subs ctx t (Rwt x (Sym s) goal)) cs
          let covered_syms = map fst cs
          let all_covered = length covered_syms >= length syms
                         && all (`elem` syms) covered_syms
          if not all_covered
            then check d span book subs ctx df goal
            else Done ()
        _ -> Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs (Enu [])) (normal 3 d book subs xT)
    (SigM x f, goal) -> do
      xT <- infer d span book subs ctx x
      case force d book subs xT of
        Sig a b -> do
          check d span book subs ctx f $ All a (Lam "x" (\h -> All (App b h) (Lam "y" (\t -> Rwt x (Tup h t) goal))))
        _ -> Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs (Sig (Var "_" 0) (Lam "_" (\_ -> Var "_" 0)))) (normal 3 d book subs xT)
    (Tup a b, Sig aT (Lam _ bT)) -> do
      check d span book subs ctx a aT
      check d span book subs ctx b (bT a)
    (Rfl, Eql t a b) -> do
      check d span book subs ctx a t
      check d span book subs ctx b t
      if equal d book subs a b
        then Done ()
        else Fail $ TermMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs a) (normal 3 d book subs b)
    -- (EqlM x f, goal) -> do
      -- xT <- infer d span book subs ctx x
      -- case force d book subs xT of
        -- Eql t a b -> do
          -- check d span book ((a,b):subs) ctx f (rewrite d book a b goal)
        -- _ -> Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0))) (normal 3 d book subs xT)
    -- Q: there is a problem in the EqlM clause above. can you identify it?
    -- A: -- A: the clause inserts the pair (a,b) into the substitution list but
    --    forgets to substitute the scrutinee variable ‘x’ with Rfl; we should
    --    add (x,Rfl) (and possibly keep (a,b) as an equality hint) otherwise
    --    ‘f’ is type-checked while ‘x’ remains free, producing an ill-typed
    --    context.
    -- fix it below:

    (EqlM x f, goal) -> do
      xT <- infer d span book subs ctx x
      case force d book subs xT of
        Eql t a b -> do
          check d span book subs ctx f (Rwt x Rfl (Rwt a b goal))
        _ -> Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0))) (normal 3 d book subs xT)

    (Fix k f, _) -> do
      check d span book subs (extend ctx k (Var k d) goal) (f (Ann (Fix k f) goal)) goal
    (Loc l t, _) -> do
      check d l book subs ctx t goal
    (Val (U64_V _), Num U64_T) -> do
      Done ()
    (Val (I64_V _), Num I64_T) -> do
      Done ()
    (Val (F64_V _), Num F64_T) -> do
      Done ()
    (Val (CHR_V _), Num CHR_T) -> do
      Done ()
    (Op2 op a b, _) -> do
      ta <- infer d span book subs ctx a
      tb <- infer d span book subs ctx b
      tr <- inferOp2Type d span book subs ctx op a b ta tb
      if equal d book subs tr goal
        then Done ()
        else Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs goal) (normal 3 d book subs tr)
    (Op1 op a, _) -> do
      ta <- infer d span book subs ctx a
      tr <- inferOp1Type d span book subs ctx op a ta
      if equal d book subs tr goal
        then Done ()
        else Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs goal) (normal 3 d book subs tr)
    (Pat _ _ _, _) -> do
      error "not-supported"
    -- (f x) :: G
    -- --------------------------------------------------- specialize
    -- f :: ∀(v : typeof x). (G where x is rewritten by v)
    (App f x, _) ->
      if isLamApp f
        then do
          xt <- infer d span book subs ctx x
          check d span book ((x,Var "_" d):subs) ctx f $ All xt $ Lam "_" $ \x -> goal
        else do
          verify d span book subs ctx term goal

    (_, _) -> do
      verify d span book subs ctx term goal

-- Verify that a term has the expected type by inference
verify :: Int -> Span -> Book -> Subs -> Ctx -> Term -> Term -> Result ()
verify d span book subs ctx term goal = do
  t <- infer d span book subs ctx term
  if equal d book subs t goal
    then Done ()
    else Fail $ TypeMismatch span (normalCtx 3 d book subs ctx) (normal 3 d book subs goal) (normal 3 d book subs t)

-- Utils
-- -----

-- Check all definitions in a Book
checkBook :: Book -> Result ()
checkBook book@(Book defs) = mapM_ checkDef (M.toList defs)
  where
    checkDef (name, (_, term, typ)) = do
      check 0 noSpan book [] (Ctx []) term typ

-- Utils
-- -----

isLamApp :: Term -> Bool
isLamApp (cut -> App f _)    = isLamApp f
isLamApp (cut -> Lam _ _)    = True
isLamApp (cut -> Efq)        = True
isLamApp (cut -> UniM _ _)   = True
isLamApp (cut -> BitM _ _ _) = True
isLamApp (cut -> NatM _ _ _) = True
isLamApp (cut -> LstM _ _ _) = True
isLamApp (cut -> EnuM _ _ _) = True
isLamApp (cut -> SigM _ _)   = True
isLamApp (cut -> EqlM _ _)   = True
isLamApp _                   = False
