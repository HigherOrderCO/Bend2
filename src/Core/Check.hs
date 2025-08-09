{-./Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Check where

import Control.Monad (unless, foldM)
import Data.List (find)
import Data.Maybe (fromJust, fromMaybe)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

import Core.Bind
import Core.Equal
import Core.Rewrite
import Core.Type
import Core.Show
import Core.WHNF

-- Utils
-- -------

extend :: Ctx -> Name -> Term -> Term -> Ctx
extend (Ctx ctx) k v t = Ctx (ctx ++ [(k, v, t)])

-- Type Checker
-- ------------

-- Infer the type of a term
infer :: Int -> Span -> Book -> Ctx -> Term -> Result Term
infer d span book@(Book funs adts names) ctx term =
  -- trace ("- infer: " ++ show d ++ " " ++ show term) $
  case term of

    -- x : T in ctx
    -- ------------ infer-Var
    -- ctx |- x : T
    Var k i -> do
      let Ctx ks = ctx
      if i < length ks
        then let (_, _, typ) = ks !! i
             in Done typ
        else Fail $ CantInfer span (normalCtx book ctx)

    -- x:T in book
    -- ------------ infer-Ref
    -- ctx |- x : T
    Ref k i -> do
      case getFun book k of
        Just fun -> Done (funType fun)
        Nothing  -> Fail $ Undefined span (normalCtx book ctx) k

    -- ctx |- x : T
    -- ------------ infer-Sub
    -- ctx |- x : T
    Sub x -> do
      infer d span book ctx x

    -- ctx        |- t : Set
    -- ctx        |- v : t
    -- ctx, v : T |- f : T
    -- -------------------------- infer-Let
    -- ctx |- (k : T = v ; f) : T
    Let k t v f -> case t of
      Just t -> do
        check d span book ctx t Set
        check d span book ctx v t
        infer (d+1) span book (extend ctx k (Var k d) t) (f (Var k d))
      Nothing -> do
        vT <- infer d span book ctx v
        infer (d+1) span book (extend ctx k (Var k d) vT) (f (Var k d))

    -- ctx |- f(v) : T
    -- -------------------------- infer-Use
    -- ctx |- (use k = v ; f) : T
    Use k v f -> do
      infer d span book ctx (f v)

    -- Can't infer Fix
    Fix k f -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- ctx |- t : Set
    -- ctx |- v : t
    -- ------------------- infer-Chk
    -- ctx |- (v :: t) : t
    Chk v t -> do
      check d span book ctx t Set
      check d span book ctx v t
      Done t

    -- ctx |-
    -- ---------------- Set
    -- ctx |- Set : Set
    Set -> do
      Done Set

    -- ctx |-
    -- ------------------ Emp
    -- ctx |- Empty : Set
    Emp -> do
      Done Set

    -- Can't infer EmpM
    EmpM -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- ctx |-
    -- ----------------- Uni
    -- ctx |- Unit : Set
    Uni -> do
      Done Set

    -- ctx |-
    -- ---------------- One
    -- ctx |- () : Unit
    One -> do
      Done Uni

    -- Can't infer UniM
    UniM f -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- ctx |-
    -- ----------------- Bit
    -- ctx |- Bool : Set
    Bit -> do
      Done Set

    -- ctx |-
    -- ------------------- Bt0
    -- ctx |- False : Bool
    Bt0 -> do
      Done Bit

    -- ctx |-
    -- ------------------ Bt1
    -- ctx |- True : Bool
    Bt1 -> do
      Done Bit

    -- Can't infer BitM
    BitM f t -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- ctx |-
    -- ---------------- Nat
    -- ctx |- Nat : Set
    Nat -> do
      Done Set

    -- ctx |-
    -- --------------- Zer
    -- ctx |- 0n : Nat
    Zer -> do
      Done Nat

    -- ctx |- n : Nat
    -- ----------------- Suc
    -- ctx |- 1n+n : Nat
    Suc n -> do
      check d span book ctx n Nat
      Done Nat

    -- Can't infer NatM
    NatM z s -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- ctx |- T : Set
    -- ---------------- Lst
    -- ctx |- T[] : Set
    Lst t -> do
      check d span book ctx t Set
      Done Set

    -- Can't infer Nil
    Nil -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- Can't infer Con
    Con h t -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- Can't infer LstM
    LstM n c -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- ctx |- p0 : T0
    -- ctx |- p1 : T1
    -- ...
    -- type T<p0:T0, p1:T1, ...> : Set in book
    -- ----------------------------------------- infer-ADT
    -- ctx |- type T<p0,p1,...> : Set
    ADT name params -> do
      case getADT book name of
        Just adt -> do
          let checkParams adt_ty [] =
                if equal d book adt_ty Set
                then Done ()
                else Fail $ CantInfer span (normalCtx book ctx) -- Should end in Set
              checkParams adt_ty (p:ps) = case force book adt_ty of
                All a b -> do
                  check d span book ctx p a
                  checkParams (App b p) ps
                _ -> Fail $ CantInfer span (normalCtx book ctx) -- Too many params
          checkParams (adtType adt) params
          Done Set
        Nothing -> Fail $ Undefined span (normalCtx book ctx) name

    -- Can't infer Ctr
    Ctr name args -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- Can't infer ADTM
    ADTM name cases def -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- ctx |- A : Set
    -- ctx |- B : ∀x:A. Set
    -- -------------------- Sig
    -- ctx |- ΣA.B : Set
    Sig a b -> do
      check d span book ctx a Set
      check d span book ctx b (All a (Lam "_" Nothing (\_ -> Set)))
      Done Set

    -- ctx |- a : A
    -- ctx |- b : B
    -- --------------------- Tup
    -- ctx |- (a,b) : Σx:A.B
    Tup a b -> do
      aT <- infer d span book ctx a
      bT <- infer d span book ctx b
      Done (Sig aT (Lam "_" Nothing (\_ -> bT)))

    -- Can't infer SigM
    SigM f -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- ctx |- A : Set
    -- ctx |- B : ∀x:A. Set
    -- -------------------- All
    -- ctx |- ∀A.B : Set
    All a b -> do
      check d span book ctx a Set
      check d span book ctx b (All a (Lam "_" Nothing (\_ -> Set)))
      Done Set

    -- ctx |- A : Set
    -- ctx, x:A |- f : B
    -- ------------------------ Lam
    -- ctx |- λx:A. f : ∀x:A. B
    Lam k t b -> case t of
      Just tk -> do
        check d span book ctx tk Set
        bT <- infer (d+1) span book (extend ctx k (Var k d) tk) (b (Var k d))
        Done (All tk (Lam k (Just tk) (\v -> bindVarByIndex d v bT)))
      Nothing -> do
        Fail $ CantInfer span (normalCtx book ctx)

    -- ctx |- f : ∀x:A. B
    -- ctx |- x : A
    -- ------------------ App
    -- ctx |- f(x) : B(x)
    App f x -> do
      fT <- infer d span book ctx f
      case force book fT of
        All fA fB -> do
          check d span book ctx x fA
          Done (App fB x)
        _ -> do
          Fail $ TypeMismatch span (normalCtx book ctx) (normal book (All (Var "_" 0) (Lam "_" Nothing (\_ -> Var "_" 0)))) (normal book fT)

    -- ctx |- t : Set
    -- ctx |- a : t
    -- ctx |- b : t
    -- ---------------------- Eql
    -- ctx |- a == b : t : Set
    Eql t a b -> do
      check d span book ctx t Set
      check d span book ctx a t
      check d span book ctx b t
      Done Set

    -- Can't infer Rfl
    Rfl -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- Can't infer EqlM
    EqlM f -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- ctx |- e : a == b : t
    -- ctx[a <- b] |- f : T[a <- b]
    -- ---------------------------- Rwt
    -- ctx |- rewrite e f : T
    Rwt e f -> do
      eT <- infer d span book ctx e
      case force book eT of
        Eql t a b -> do
          let rewrittenCtx = rewriteCtx d book a b ctx
          infer d span book rewrittenCtx f
        _ ->
          Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0))) (normal book eT)

    -- ctx |- t : T
    -- ------------ Loc
    -- ctx |- t : T
    Loc l t ->
      infer d l book ctx t

    -- Can't infer Era
    Era -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- Can't infer Sup
    Sup l a b -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- Can't infer SupM
    SupM l f -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- Can't infer Frk
    Frk l a b -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- Can't infer Met
    Met n t c -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- ctx |-
    -- -------------- Num
    -- ctx |- T : Set
    Num t -> do
      Done Set

    -- ctx |-
    -- -------------- Val-U64
    -- ctx |- n : U64
    Val (U64_V v) -> do
      Done (Num U64_T)

    -- ctx |-
    -- -------------- Val-I64
    -- ctx |- n : I64
    Val (I64_V v) -> do
      Done (Num I64_T)

    -- ctx |-
    -- -------------- Val-F64
    -- ctx |- n : F64
    Val (F64_V v) -> do
      Done (Num F64_T)

    -- ctx |-
    -- --------------- Val-CHR
    -- ctx |- c : Char
    Val (CHR_V v) -> do
      Done (Num CHR_T)

    -- ctx |- a : ta
    -- ctx |- b : tb
    -- inferOp2Type op ta tb = tr
    -- --------------------------- Op2
    -- ctx |- a op b : tr
    Op2 op a b -> do
      ta <- infer d span book ctx a
      tb <- infer d span book ctx b
      inferOp2Type d span book ctx op ta tb

    -- ctx |- a : ta
    -- inferOp1Type op ta = tr
    -- ----------------------- Op1
    -- ctx |- op a : tr
    Op1 op a -> do
      ta <- infer d span book ctx a
      inferOp1Type d span book ctx op ta

    -- ctx |-
    -- -------------------------------- Pri-U64_TO_CHAR
    -- ctx |- U64_TO_CHAR : U64 -> Char
    Pri U64_TO_CHAR -> do
      Done (All (Num U64_T) (Lam "x" Nothing (\_ -> Num CHR_T)))

    -- ctx |-
    -- -------------------------------- Pri-CHAR_TO_U64
    -- ctx |- CHAR_TO_U64 : Char -> U64
    Pri CHAR_TO_U64 -> do
      Done (All (Num CHR_T) (Lam "x" Nothing (\_ -> Num U64_T)))

    -- Can't infer HVM priority change primitives
    Pri HVM_INC -> do
      Fail $ CantInfer span (normalCtx book ctx)
    Pri HVM_DEC -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- ctx |- s : Char[]
    -- ctx |- x : T
    -- ------------------ Log
    -- ctx |- log s x : T
    Log s x -> do
      check d span book ctx s (Lst (Num CHR_T))
      infer d span book ctx x

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
      (Num t1, Num t2) | t1 == t2 -> Done (Num t1)
      (Nat, Nat) -> Done Nat  -- Allow Nat arithmetic operations
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Ref "Num" 1)) (normal book ta)

    comparisonOp ta tb = case (force book ta, force book tb) of
      (Num t1, Num t2) | t1 == t2 -> Done Bit
      (Bit, Bit) -> Done Bit  -- Allow Bool comparison
      (Nat, Nat) -> Done Bit  -- Allow Nat comparison
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book ta) (normal book tb)

    integerOp ta tb = case (force book ta, force book tb) of
      (Num U64_T, Num U64_T) -> Done (Num U64_T)
      (Num I64_T, Num I64_T) -> Done (Num U64_T)  -- Bitwise on I64 returns U64
      (Num F64_T, Num F64_T) -> Done (Num U64_T)  -- Bitwise on F64 returns U64
      (Num CHR_T, Num CHR_T) -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Ref "Num" 1)) (normal book ta)  -- Bitwise not supported for CHR
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Ref "Num" 1)) (normal book ta)

    boolOrIntegerOp ta tb = case (force book ta, force book tb) of
      (Bit, Bit) -> Done Bit  -- Logical operations on booleans
      (Num U64_T, Num U64_T) -> Done (Num U64_T)  -- Bitwise operations on integers
      (Num I64_T, Num I64_T) -> Done (Num U64_T)
      (Num F64_T, Num F64_T) -> Done (Num U64_T)
      _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book ta) (normal book tb)

-- Infer the result type of a unary numeric operation
inferOp1Type :: Int -> Span -> Book -> Ctx -> NOp1 -> Term -> Result Term
inferOp1Type d span book ctx op ta = case op of
  NOT -> case force book ta of
    Bit       -> Done Bit  -- Logical NOT on Bool
    Num U64_T -> Done (Num U64_T)
    Num I64_T -> Done (Num U64_T)  -- Bitwise NOT on I64 returns U64
    Num F64_T -> Done (Num U64_T)  -- Bitwise NOT on F64 returns U64
    Num CHR_T -> Fail $ CantInfer span (normalCtx book ctx)  -- Bitwise NOT not supported for CHR
    _         -> Fail $ CantInfer span (normalCtx book ctx)
  NEG -> case force book ta of
    Num I64_T -> Done (Num I64_T)
    Num F64_T -> Done (Num F64_T)
    Num CHR_T -> Fail $ CantInfer span (normalCtx book ctx)  -- Negation not supported for CHR
    _         -> Fail $ CantInfer span (normalCtx book ctx)

-- Check if a term has the expected type
check :: Int -> Span -> Book -> Ctx -> Term -> Term -> Result ()
check d span book ctx (Loc l t) goal = check d l book ctx t goal
check d span book ctx term      goal =
  -- trace ("- check: " ++ show d ++ " " ++ show term ++ " :: " ++ show (force book (normal book goal))) $
  case (term, force book goal) of
    -- ctx |-
    -- ----------- Era
    -- ctx |- * : T
    (Era, _) -> do
      Done ()

    -- ctx |- t : Set
    -- ctx |- v : t
    -- ctx, x:t |- f : T
    -- ------------------------- Let
    -- ctx |- (x : t = v ; f) : T
    (Let k t v f, _) -> case t of
        Just t  -> do
          check d span book ctx t Set
          check d span book ctx v t
          check (d+1) span book (extend ctx k (Var k d) t) (f (Var k d)) goal
        Nothing -> do
          vT <- infer d span book ctx v
          check (d+1) span book (extend ctx k (Var k d) vT) (f (Var k d)) goal

    -- ctx |- f(v) : T
    -- -------------------------- Use
    -- ctx |- (use k = v ; f) : T
    (Use k v f, _) -> do
      check d span book ctx (f v) goal

    -- ctx |-
    -- ---------------- One
    -- ctx |- () : Unit
    (One, Uni) -> do
      Done ()

    -- ctx |-
    -- ------------------- Bt0
    -- ctx |- False : Bool
    (Bt0, Bit) -> do
      Done ()

    -- ctx |-
    -- ------------------ Bt1
    -- ctx |- True : Bool
    (Bt1, Bit) -> do
      Done ()

    -- ctx |-
    -- --------------- Zer
    -- ctx |- 0n : Nat
    (Zer, Nat) -> do
      Done ()

    -- ctx |- n : Nat
    -- ----------------- Suc
    -- ctx |- 1n+n : Nat
    (Suc n, Nat) -> do
      check d span book ctx n Nat

    -- ctx |- n : a==b:t
    -- --------------------------- Suc-Eql
    -- ctx |- 1n+n : 1n+a==1n+b:t
    (Suc n, Eql t (force book -> Suc a) (force book -> Suc b)) -> do
      check d span book ctx n (Eql t a b)

    -- ctx |-
    -- --------------- Nil
    -- ctx |- [] : T[]
    (Nil, Lst t) -> do
      Done ()

    -- Type mismatch for Nil
    (Nil, goal) ->
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Lst (Var "_" 0))) (normal book goal)

    -- ctx |- h : T
    -- ctx |- t : T[]
    -- ------------------ Con
    -- ctx |- h<>t : T[]
    (Con h t, Lst tT) -> do
      check d span book ctx h tT
      check d span book ctx t (Lst tT)

    -- ctx |- h : h1==h2:T
    -- ctx |- t : t1==t2:T[]
    -- --------------------------------- Con-Eql
    -- ctx |- h<>t : h1<>t1==h2<>t2:T[]
    (Con h t, Eql (force book -> Lst tT) (force book -> Con h1 t1) (force book -> Con h2 t2)) -> do
      check d span book ctx h (Eql tT h1 h2)
      check d span book ctx t (Eql (Lst tT) t1 t2)

    -- K{v0,v1,...} : type T<p0,p1,...> if
    -- K is a constructor of T with type λP. ∀x0:T0 x1:T1 ... P(K{x0,x1,...})
    -- ctx |- v0 : T0
    -- ctx |- v1 : T1[x0:=v0]
    -- ...
    -- ---------------------------------------- check-Ctr
    -- ctx |- K{v0,v1,...} : type T<p0,p1,...>
    (Ctr cname cargs, force book -> ADT adtName params) -> do
      case getADT book adtName of
        Just adt ->
          case find (\(name,_) -> name == cname) (adtCtrs adt) of
            Just (_, ctrType) -> do
              -- The motive returns the goal type for any constructed value
              let motive = Lam "_" Nothing (\_ -> ADT adtName params)
              -- Apply the constructor type to the ADT parameters and then to the motive
              let applyParams ty [] = App ty motive
                  applyParams ty (p:ps) = applyParams (App ty p) ps
              let ctr_full_type = force book (applyParams ctrType params)
              -- Check arguments against the quantified types
              let checkArgs ty args = case (force book ty, args) of
                    (All a b, arg:rest) -> do
                      check d span book ctx arg a
                      checkArgs (App b arg) rest
                    (_, []) -> Done ()
                    (_, _:_) -> Fail $ CantInfer span (normalCtx book ctx)
              checkArgs ctr_full_type cargs
            Nothing -> Fail $ Undefined span (normalCtx book ctx) cname
        Nothing -> Fail $ Undefined span (normalCtx book ctx) adtName

    -- K{v0,v1,...} : (K{u0,u1,...} == K{w0,w1,...} : type T<...>) if
    -- K is a constructor of T with type λP. ∀x0:T0 x1:T1 ... P(K{x0,x1,...})
    -- ctx |- v0 : (u0 == w0 : T0)
    -- ctx |- v1 : (u1 == w1 : T1[x0:=v0])
    -- ...
    -- ---------------------------------------- check-Ctr-Eql
    -- ctx |- K{v0,v1,...} : (K{u0,u1,...} == K{w0,w1,...} : type T<...>)
    (Ctr cname cargs, Eql (force book -> ADT adtName params) (force book -> Ctr cname1 cargs1) (force book -> Ctr cname2 cargs2)) -> do
      if cname == cname1 && cname1 == cname2 && length cargs == length cargs1 && length cargs1 == length cargs2 then do
        case getADT book adtName of
          Just adt ->
            case find (\(name,_) -> name == cname) (adtCtrs adt) of
              Just (_, ctrType) -> do
                let motive = Lam "_" Nothing (\_ -> ADT adtName params)
                -- Apply the constructor type to the ADT parameters and then to the motive
                let applyParams ty [] = App ty motive
                    applyParams ty (p:ps) = applyParams (App ty p) ps
                let ctr_full_type = applyParams ctrType params
                let checkEqArgs ty args args1 args2 = case (force book ty, args, args1, args2) of
                      (All a b, arg:restArgs, arg1:restArgs1, arg2:restArgs2) -> do
                        check d span book ctx arg (Eql a arg1 arg2)
                        checkEqArgs (App b arg) restArgs restArgs1 restArgs2
                      (_, [], [], []) -> Done ()
                      _ -> Fail $ CantInfer span (normalCtx book ctx)
                checkEqArgs ctr_full_type cargs cargs1 cargs2
              Nothing -> Fail $ Undefined span (normalCtx book ctx) cname
          Nothing -> Fail $ Undefined span (normalCtx book ctx) adtName
      else
        Fail $ TermMismatch span (normalCtx book ctx) (normal book (Ctr cname1 cargs1)) (normal book (Ctr cname2 cargs2))

    -- Type mismatch for Ctr
    (Ctr cname args, _) -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- ctx, x:A |- f : B
    -- ---------------------- Lam
    -- ctx |- λx. f : ∀x:A. B
    (Lam k t f, All a b) -> do
      check (d+1) span book (extend ctx k (Var k d) a) (f (Var k d)) (App b (Var k d))

    -- ctx |-
    -- --------------------------------- EmpM-Eql-Zer-Suc
    -- ctx |- λ{} : ∀p:(0n==1n+y:t). R(p)
    (EmpM, All (force book -> Eql t (force book -> Zer) (force book -> Suc y)) rT) -> do
      Done ()

    -- ctx |-
    -- --------------------------------- EmpM-Eql-Suc-Zer
    -- ctx |- λ{} : ∀p:(1n+x==0n:t). R(p)
    (EmpM, All (force book -> Eql t (force book -> Suc x) (force book -> Zer)) rT) -> do
      Done ()

    -- ctx |- λ{} : ∀p:(x==y:t). R(p)
    -- ----------------------------------- EmpM-Eql-Suc-Suc
    -- ctx |- λ{} : ∀p:(1n+x==1n+y:t). R(p)
    (EmpM, All (force book -> Eql t (force book -> Suc x) (force book -> Suc y)) rT) -> do
      check d span book ctx EmpM (All (Eql t x y) rT)

    -- ctx |-
    -- ------------------------ EmpM-Emp
    -- ctx |- λ{} : ∀x:Empty. R
    (EmpM, All (force book -> Emp) rT) -> do
      Done ()

    -- Type mismatch for EmpM
    (EmpM, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Emp (Lam "_" Nothing (\_ -> Set))))

    -- ctx |- f : R({==})
    -- -------------------------------------- UniM-Eql
    -- ctx |- λ{():f} : ∀p:(()==():Unit). R(p)
    (UniM f, All (force book -> Eql (force book -> Uni) (force book -> One) (force book -> One)) rT) -> do
      check d span book ctx f (App rT Rfl)

    -- ctx |- f : R(())
    -- --------------------------- UniM
    -- ctx |- λ{():f} : ∀x:Unit. R
    (UniM f, All (force book -> Uni) rT) -> do
      check d span book ctx f (App rT One)

    -- Type mismatch for UniM
    (UniM f, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Uni (Lam "_" Nothing (\_ -> Set))))

    -- ctx |- f : R({==})
    -- ------------------------------------------------------ BitM-Eql-Bt0-Bt0
    -- ctx |- λ{False:f;True:t} : ∀p:(False==False:Bool). R(p)
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt0) (force book -> Bt0)) rT) -> do
      check d span book ctx f (App rT Rfl)

    -- ctx |- t : R({==})
    -- ---------------------------------------------------- BitM-Eql-Bt1-Bt1
    -- ctx |- λ{False:f;True:t} : ∀p:(True==True:Bool). R(p)
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt1) (force book -> Bt1)) rT) -> do
      check d span book ctx t (App rT Rfl)

    -- ctx |-
    -- ----------------------------------------------------- BitM-Eql-Bt0-Bt1
    -- ctx |- λ{False:f;True:t} : ∀p:(False==True:Bool). R(p)
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt0) (force book -> Bt1)) rT) -> do
      Done ()

    -- ctx |-
    -- ----------------------------------------------------- BitM-Eql-Bt1-Bt0
    -- ctx |- λ{False:f;True:t} : ∀p:(True==False:Bool). R(p)
    (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt1) (force book -> Bt0)) rT) -> do
      Done ()

    -- ctx |- f : R(False)
    -- ctx |- t : R(True)
    -- ------------------------------------- BitM
    -- ctx |- λ{False:f;True:t} : ∀x:Bool. R
    (BitM f t, All (force book -> Bit) rT) -> do
      check d span book ctx f (App rT Bt0)
      check d span book ctx t (App rT Bt1)

    -- Type mismatch for BitM
    (BitM f t, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Bit (Lam "_" Nothing (\_ -> Set))))

    -- ctx |- z : R({==})
    -- ------------------------------------------- NatM-Eql-Zer-Zer
    -- ctx |- λ{0n:z;1n+:s} : ∀p:(0n==0n:Nat). R(p)
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Zer) (force book -> Zer)) rT) -> do
      check d span book ctx z (App rT Rfl)

    -- ctx |- s : ∀p:(a==b:Nat). R(1n+p)
    -- ----------------------------------------------- NatM-Eql-Suc-Suc
    -- ctx |- λ{0n:z;1n+:s} : ∀p:(1n+a==1n+b:Nat). R(p)
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Suc a) (force book -> Suc b)) rT) -> do
      check d span book ctx s (All (Eql Nat a b) (Lam "p" Nothing (\p -> App rT (Suc p))))

    -- ctx |-
    -- --------------------------------------------- NatM-Eql-Zer-Suc
    -- ctx |- λ{0n:z;1n+:s} : ∀p:(0n==1n+_:Nat). R(p)
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Zer) (force book -> Suc _)) rT) -> do
      Done ()

    -- ctx |-
    -- --------------------------------------------- NatM-Eql-Suc-Zer
    -- ctx |- λ{0n:z;1n+:s} : ∀p:(1n+_==0n:Nat). R(p)
    (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Suc _) (force book -> Zer)) rT) -> do
      Done ()

    -- ctx |- z : R(0n)
    -- ctx |- s : ∀p:Nat. R(1n+p)
    -- -------------------------------- NatM
    -- ctx |- λ{0n:z;1n+:s} : ∀x:Nat. R
    (NatM z s, All (force book -> Nat) rT) -> do
      check d span book ctx z (App rT Zer)
      check d span book ctx s (All Nat (Lam "p" Nothing (\p -> App rT (Suc p))))

    -- Type mismatch for NatM
    (NatM z s, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Nat (Lam "_" Nothing (\_ -> Set))))

    -- ctx |- n : R({==})
    -- ------------------------------------------ LstM-Eql-Nil-Nil
    -- ctx |- λ{[]:n;<>:c} : ∀p:([]==[]:T[]). R(p)
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Nil) (force book -> Nil)) rT) -> do
      check d span book ctx n (App rT Rfl)

    -- ctx |- c : ∀hp:(h1==h2:T). ∀tp:(t1==t2:T[]). R(hp<>tp)
    -- ---------------------------------------------------- LstM-Eql-Con-Con
    -- ctx |- λ{[]:n;<>:c} : ∀p:(h1<>t1==h2<>t2:T[]). R(p)
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Con h1 t1) (force book -> Con h2 t2)) rT) -> do
      check d span book ctx c (All (Eql a h1 h2) (Lam "hp" Nothing (\hp ->
        All (Eql (Lst a) t1 t2) (Lam "tp" Nothing (\tp ->
          App rT (Con hp tp))))))

    -- ctx |-
    -- -------------------------------------------- LstM-Eql-Nil-Con
    -- ctx |- λ{[]:n;<>:c} : ∀p:([]==_<>_:T[]). R(p)
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Nil) (force book -> Con _ _)) rT) -> do
      Done ()

    -- ctx |-
    -- -------------------------------------------- LstM-Eql-Con-Nil
    -- ctx |- λ{[]:n;<>:c} : ∀p:(_<>_==[]:T[]). R(p)
    (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Con _ _) (force book -> Nil)) rT) -> do
      Done ()

    -- ctx |- n : R([])
    -- ctx |- c : ∀h:T. ∀t:T[]. R(h<>t)
    -- -------------------------------- LstM
    -- ctx |- λ{[]:n;<>:c} : ∀x:T[]. R
    (LstM n c, All (force book -> Lst a) rT) -> do
      check d span book ctx n (App rT Nil)
      check d span book ctx c $ All a (Lam "h" Nothing (\h -> All (Lst a) (Lam "t" Nothing (\t -> App rT (Con h t)))))

    -- Type mismatch for LstM
    (LstM n c, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Lst (Var "_" 0)) (Lam "_" Nothing (\_ -> Set))))

    -- Check ADTM against a function type
    -- For each constructor K with type λP. ∀x0:T0 x1:T1 ... P(K{x0,x1,...})
    -- Check the case for K : ∀x0:T0 x1:T1 ... rT(K{x0,x1,...})
    -- If there's a default case, check it : ∀x:(type T<...>). rT(x)
    (ADTM adtName cases defCase, All adt_type@(force book -> ADT adtName' params) rT) | adtName == adtName' -> do
      case getADT book adtName of
        Just adt -> do
          -- Check each constructor case
          mapM_ (checkCase adt) cases
          -- Check default case if it exists
          case defCase of
            Just defTerm -> do
              check d span book ctx defTerm (All adt_type (Lam "_" Nothing (\v -> App rT v)))
            Nothing -> do
              -- If no default case, check that all constructors are covered
              let allCtrNames  = S.fromList $ map fst (adtCtrs adt)
              let coveredNames = S.fromList $ map fst cases
              if allCtrNames == coveredNames
                then Done ()
                else Fail $ IncompleteMatch span (normalCtx book ctx)
          where
            checkCase adt (ctrName, caseTerm) = do
              case find (\(name,_) -> name == ctrName) (adtCtrs adt) of
                Just (_, ctrType) -> do
                  -- Apply the constructor type to the ADT parameters and then to rT
                  let applyParams ty [] = App ty rT
                      applyParams ty (p:ps) = applyParams (App ty p) ps
                  let expectedType = applyParams ctrType params
                  check d span book ctx caseTerm expectedType
                Nothing -> Fail $ Undefined span (normalCtx book ctx) ctrName
        Nothing -> Fail $ Undefined span (normalCtx book ctx) adtName

    -- Type mismatch for ADTM
    (ADTM _ _ _, _) -> do
      Fail $ CantInfer span (normalCtx book ctx)

    -- ctx |- f : ∀xp:(x1==x2:A). ∀yp:(y1==y2:B(x1)). R((xp,yp))
    -- ------------------------------------------------------- SigM-Eql
    -- ctx |- λ{(,):f} : ∀p:((x1,y1)==(x2,y2):ΣA.B). R(p)
    (SigM f, All (force book -> Eql (force book -> Sig a b) (force book -> Tup x1 y1) (force book -> Tup x2 y2)) rT) -> do
      check d span book ctx f (All (Eql a x1 x2) (Lam "xp" Nothing (\xp ->
        All (Eql (App b x1) y1 y2) (Lam "yp" Nothing (\yp ->
          App rT (Tup xp yp))))))

    -- ctx |- f : ∀x:A. ∀y:B(x). R((x,y))
    -- ----------------------------------- SigM
    -- ctx |- λ{(,):f} : ∀p:ΣA.B. R
    (SigM f, All (force book -> Sig a b) rT) -> do
      check d span book ctx f $ All a (Lam "x" Nothing (\h -> All (App b h) (Lam "y" Nothing (\t -> App rT (Tup h t)))))

    -- Type mismatch for SigM
    (SigM f, _) -> do
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Sig (Var "_" 0) (Lam "_" Nothing (\_ -> Var "_" 0))) (Lam "_" Nothing (\_ -> Set))))

    -- ctx |- a : A
    -- ctx |- b : B(a)
    -- ------------------- Tup
    -- ctx |- (a,b) : ΣA.B
    (Tup a b, Sig aT bT) -> do
      check d span book ctx a aT
      check d span book ctx b (App bT a)

    -- ctx |- a : a1==a2:A
    -- ctx |- b : b1==b2:B(a1)
    -- ------------------------------------- Tup-Eql
    -- ctx |- (a,b) : (a1,b1)==(a2,b2):ΣA.B
    (Tup a b, Eql (force book -> Sig aT bT) (force book -> Tup a1 b1) (force book -> Tup a2 b2)) -> do
      check d span book ctx a (Eql aT a1 a2)
      check d span book ctx b (Eql (App bT a1) b1 b2)

    -- equal a b
    -- --------------------- Rfl
    -- ctx |- {==} : a==b:T
    (Rfl, Eql t a b) -> do
      if equal d book a b
        then Done ()
        else Fail $ TermMismatch span (normalCtx book ctx) (normal book a) (normal book b)

    -- ctx[a <- b] |- f : R({==})[a <- b]
    -- ----------------------------------- EqlM
    -- ctx |- λ{{==}:f} : ∀p:(a==b:T). R(p)
    (EqlM f, All (force book -> Eql t a b) rT) -> do
      let rewrittenGoal = rewrite d book a b (App rT Rfl)
      let rewrittenCtx  = rewriteCtx d book a b ctx
      check d span book rewrittenCtx f rewrittenGoal

    -- ctx, k:T |- f : T
    -- ----------------- Fix
    -- ctx |- μk. f : T
    (Fix k f, _) -> do
      check (d+1) span book (extend ctx k (Fix k f) goal) (f (Fix k f)) goal

    -- ctx |-
    -- -------------- Val-U64
    -- ctx |- n : U64
    (Val v@(U64_V _), Num U64_T) -> do
      Done ()

    -- ctx |-
    -- -------------- Val-I64
    -- ctx |- n : I64
    (Val v@(I64_V _), Num I64_T) -> do
      Done ()

    -- ctx |-
    -- -------------- Val-F64
    -- ctx |- n : F64
    (Val v@(F64_V _), Num F64_T) -> do
      Done ()

    -- ctx |-
    -- --------------- Val-CHR
    -- ctx |- c : Char
    (Val v@(CHR_V _), Num CHR_T) -> do
      Done ()

    -- v1 == v2, v2 == v3
    -- --------------------- Val-Eql
    -- ctx |- v1 : v2==v3:T
    (Val v1, Eql (force book -> Num t) (force book -> Val v2) (force book -> Val v3)) -> do
      if v1 == v2 && v2 == v3
        then Done ()
        else Fail $ TermMismatch span (normalCtx book ctx) (normal book (Val v2)) (normal book (Val v3))

    -- ctx |- a : ta
    -- ctx |- b : tb
    -- inferOp2Type op ta tb = tr
    -- equal tr goal
    -- --------------------------- Op2
    -- ctx |- a op b : goal
    (Op2 op a b, _) -> do
      ta <- infer d span book ctx a
      tb <- infer d span book ctx b
      tr <- inferOp2Type d span book ctx op ta tb
      if equal d book tr goal
        then Done ()
        else Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book tr)

    -- ctx |- a : ta
    -- inferOp1Type op ta = tr
    -- equal tr goal
    -- ----------------------- Op1
    -- ctx |- op a : goal
    (Op1 op a, _) -> do
      ta <- infer d span book ctx a
      tr <- inferOp1Type d span book ctx op ta
      if equal d book tr goal
        then Done ()
        else Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book tr)

    -- ctx |- a : T
    -- ctx |- b : T
    -- ------------------ Sup
    -- ctx |- &L{a,b} : T
    (Sup l a b, _) -> do
      check d span book ctx a goal
      check d span book ctx b goal

    -- equal l l1, equal l1 l2
    -- ctx |- f : ∀ap:(a1==a2:T). ∀bp:(b1==b2:T). R(&l{ap,bp})
    -- ------------------------------------------------------ SupM-Eql
    -- ctx |- λ{&l{,}:f} : ∀p:(&l1{a1,b1}==&l2{a2,b2}:T). R(p)
    (SupM l f, All (force book -> Eql t (force book -> Sup l1 a1 b1) (force book -> Sup l2 a2 b2)) rT) -> do
      if equal d book l l1 && equal d book l1 l2
        then do
          check d span book ctx f (All (Eql t a1 a2) (Lam "ap" Nothing (\ap ->
                 All (Eql t b1 b2) (Lam "bp" Nothing (\bp ->
                   App rT (Sup l ap bp))))))
        else Fail $ TermMismatch span (normalCtx book ctx) (normal book l1) (normal book l2)

    -- ctx |- l : U64
    -- ctx |- f : ∀p:T. ∀q:T. R(&l{p,q})
    -- --------------------------------- SupM
    -- ctx |- λ{&l{,}:f} : ∀x:T. R
    (SupM l f, _) -> do
      check d span book ctx l (Num U64_T)
      case force book goal of
        All xT rT -> do
          check d span book ctx f (All xT (Lam "p" Nothing (\p -> All xT (Lam "q" Nothing (\q -> App rT (Sup l p q))))))
        _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Var "_" 0) (Lam "_" Nothing (\_ -> Set))))

    -- ctx |- l : U64
    -- ctx |- a : T
    -- ctx |- b : T
    -- -------------------------- Frk
    -- ctx |- fork l:a else:b : T
    (Frk l a b, _) -> do
      check d span book ctx l (Num U64_T)
      check d span book ctx a goal
      check d span book ctx b goal

    -- ctx |- e : a==b:T
    -- ctx[a <- b] |- f : goal[a <- b]
    -- ------------------------------- Rwt
    -- ctx |- rewrite e f : goal
    (Rwt e f, _) -> do
      eT <- infer d span book ctx e
      case force book eT of
        Eql t a b -> do
          let rewrittenCtx  = rewriteCtx d book a b ctx
          let rewrittenGoal = rewrite d book a b goal
          check d span book rewrittenCtx f rewrittenGoal
        _ ->
          Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0))) (normal book eT)

    -- Not supported
    (Pat _ _ _, _) -> do
      error "not-supported"

    -- ctx |- s : Char[]
    -- ctx |- x : T
    -- ------------------ Log
    -- ctx |- log s x : T
    (Log s x, _) -> do
      check d span book ctx s (Lst (Num CHR_T))
      check d span book ctx x goal

    -- ctx |- x : T
    -- ------------------ HVM_INC
    -- ctx |- HVM_INC x : T
    (App (Pri HVM_INC) x, _) ->
      check d span book ctx x goal

    -- ctx |- x : T
    -- ------------------ HVM_DEC
    -- ctx |- HVM_DEC x : T
    (App (Pri HVM_DEC) x, _) ->
      check d span book ctx x goal

    -- Type mismatch for Lam
    (Lam f t x, _) ->
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (Ref "Function" 1)

    -- Default case: try to infer and verify
    (term, _) -> do
      let (fn, xs) = collectApps term []
      if isLam fn then do
        Fail $ Unsupported span (normalCtx book ctx)
      else do
        verify d span book ctx term goal

-- Verify that a term has the expected type by inference
verify :: Int -> Span -> Book -> Ctx -> Term -> Term -> Result ()
verify d span book ctx term goal = do
  t <- infer d span book ctx term
  if equal d book t goal
    then Done ()
    else Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book t)

