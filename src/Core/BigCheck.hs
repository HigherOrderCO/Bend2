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
import Core.FreeVars
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

data Constraint = 
  Constr Term Term
  deriving Show

data Subst = Subst Int Term
  deriving Show

-- getSubsts :: Int -> Book -> [Constraint] -> [Subst] -> ([Constraint], [Subst])
-- getSubsts d book [] substitutions = ([],substitutions)
-- getSubsts d book ((Constr (Var k i) term):constraints) substitutions = getSubsts d book constraints (Subst i term:substitutions)
-- getSubsts d book ((Constr term (Var k i)):constraints) substitutions = getSubsts d book constraints (Subst i term:substitutions)
-- getSubsts d book ((Constr a b):constraints) substitutions | eql False d book a b = getSubsts d book constraints substitutions
-- getSubsts d book constraints substitutions = error $ "undefined subst: "  ++ show constraints ++ " -- " ++ show substitutions
getSubsts :: Int -> Span -> Book -> Ctx -> [Constraint] -> [Subst] -> Result ([Constraint], [Subst])
getSubsts d span book ctx [] substitutions = return ([],substitutions)
getSubsts d span book ctx ((Constr (Var k i) term):constraints) substitutions = getSubsts d span book ctx constraints (Subst i term:substitutions)
getSubsts d span book ctx ((Constr term (Var k i)):constraints) substitutions = getSubsts d span book ctx constraints (Subst i term:substitutions)
getSubsts d span book ctx ((Constr a b):constraints) substitutions | eql False d book a b = getSubsts d span book ctx constraints substitutions
-- getSubsts d book constraints substitutions = error $ "undefined subst: "  ++ show constraints ++ " -- " ++ show substitutions
getSubsts d span book ctx ((Constr a b):constraints) substitutions = Fail $ CantInfer span (normalCtx book ctx) 
                                                                        (Just $ "Unsolvable constraint: " ++ show a ++ " == " ++ show b)
doSubsts :: [Subst] -> Term -> Term
doSubsts substitutions term = case go substitutions term of
  ([], t) -> t
  _       -> error "undefined"
  where
    go [] term = ([], term)
    go (Subst i val:substitutions) term = go (map (rewriteSubst i val) substitutions) (bindVarByIndex i val term)
    rewriteSubst i val (Subst i' val') = Subst i' (bindVarByIndex i val val')

infer :: Int -> Span -> Book -> Ctx -> Term -> Maybe Term -> Result Term
infer d span book ctx term environment = 
  -- trace ("infer " ++ show term ++ " @ " ++ show environment) $ 
  do
  (typeWithNewVars, constraints, _) <- inferWithConstraints d span book ctx (cut term) (-1)
  (_, substs) <- getSubsts d span book ctx constraints []
  let termType = doSubsts substs typeWithNewVars
  if any (\case ('?':_) -> True; _ -> False) (S.toList (freeVars S.empty termType))
  then Fail $ CantInfer span (normalCtx book ctx) Nothing
  else do
    -- traceM $ "infered with constraints that " ++ show term ++ " :: " ++ show termType
    return termType
inferVarInEnv :: Int -> Span -> Book -> Ctx -> Name -> Body -> Result Term
inferVarInEnv d span book ctx k environment = 
  -- trace ("infer in env " ++ show (Var k d) ++ " @ " ++ show (environment (Var k d))) $ 
  do
  (typeWithNewVars, constraints, _) <- inferWithConstraints d span book ctx (Lam k Nothing environment) (-1)
  case typeWithNewVars of
    All kT _ -> do
      (_, substs) <- getSubsts d span book ctx constraints []
      let termType = doSubsts substs kT
      return termType
    _ -> Fail $ CantInfer span (normalCtx book ctx) Nothing

inferWithConstraints :: Int -> Span -> Book -> Ctx -> Term -> Int -> Result (Term, [Constraint], Int)
inferWithConstraints d span book ctx term@(Loc _ t) idx = inferWithConstraints d span book ctx t idx
inferWithConstraints d span book ctx term@(Bit) idx = return (Set, [], idx)
inferWithConstraints d span book ctx term@(Bt0) idx = return (Bit, [], idx)
inferWithConstraints d span book ctx term@(Bt1) idx = return (Bit, [], idx)
inferWithConstraints d span book ctx term@(Nat) idx = return (Set, [], idx)
inferWithConstraints d span book ctx term@(Suc n) idx = 
  do
  (nT, n_cnstr, idx1) <- inferWithConstraints d span book ctx n idx
  return (Nat, [Constr nT Nat] ++ n_cnstr, idx1)
-- inferWithConstraints d span book ctx term@(Suc n) idx = 
--   -- trace ("infer constraints VAR: " ++ show term) $ do
--   case check d span book ctx n Nat of
--     Done n' -> return (Nat, [], idx)
--     _       -> Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(Var ('?':_) i) idx = return (Set, [], idx)
inferWithConstraints d span book ctx term@(Var k i) idx =
  -- trace ("infer constraints VAR: " ++ show term) $ 
  do
  let Ctx ks = ctx
  if i < length ks && i >= 0
    then let (_, _, typ) = ks !! i
         in return (typ, [], idx)
    else Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(Ref k i) idx =
  -- trace ("infer constraints REF: " ++ show term) $ 
  do
  case getDefn book k of
    Just (_, _, typ) -> return (typ, [], idx)
    Nothing          -> Fail $ Undefined span (normalCtx book ctx) k Nothing
inferWithConstraints d span book ctx term@(Lam k (Just t) body) idx = 
  do
  let new_ctx = extend ctx k (Var k d) (Var ("?"++k) idx)
  (bodyType, inner_constraints, idx1) <- inferWithConstraints (d+1) span book new_ctx (body (Var k d)) (idx-1)
  let termType = All (Var ("?"++k) idx) (Lam k Nothing (\v -> bindVarByIndex d v bodyType))
  return (termType, inner_constraints ++ [], idx1)
inferWithConstraints d span book ctx term@(Lam k Nothing body) idx = 
  -- trace ("infer constraints LAM: " ++ show term) $ 
  do
  let new_ctx = extend ctx k (Var k d) (Var ("?"++k) idx)
  (bodyType, inner_constraints, idx1) <- inferWithConstraints (d+1) span book new_ctx (body (Var k d)) (idx-1)
  let termType = All (Var ("?"++k) idx) (Lam k Nothing (\v -> bindVarByIndex d v bodyType))
  return (termType, inner_constraints ++ [], idx1)
inferWithConstraints d span book ctx term@(App f x) idx = 
  -- trace ("infer constraints APP " ++ show term) $ 
  do
    case inferWithConstraints d span book ctx f idx of
      Done (cut -> All aT bT, f_ctrs, idx1) -> do
        (xT, x_ctrs, idx2) <- inferWithConstraints d span book ctx x idx1
        case cut bT of
          Lam _ _ bT' -> return $ ((bT' x), [Constr xT aT] ++ f_ctrs ++ x_ctrs, idx2) -- TODO: correct?
          _           -> return $ (App bT x, [Constr xT aT] ++ f_ctrs ++ x_ctrs, idx2)
      Done (cut -> App f' x', f_ctrs, idx1) -> do
        let typ = appToFirstArg (App f' x') x
        (xT, x_ctrs, idx2) <- inferWithConstraints d span book ctx x idx1
        let aT = get_aT d f'
        return $ (typ, [Constr aT xT] ++ f_ctrs ++ x_ctrs, idx2)
        where
          appToFirstArg (Loc l t)    x = appToFirstArg t x
          appToFirstArg (App g y)    x = App (appToFirstArg g x) y
          appToFirstArg (Lam k mt b) x = Lam k mt (\v -> appToFirstArg (b v) x)
          appToFirstArg (BitM f t) x   = BitM (appToFirstArg f x) (appToFirstArg t x)
          appToFirstArg (All aT bT)  x = App bT x
          appToFirstArg term x  = error $ "undefined appToFirstArg " ++ show term ++ " on " ++ show x
          get_aT d (Loc l t)    = get_aT d t
          get_aT d (App g y)    = get_aT d g
          get_aT d (Lam k mt b) = get_aT (d+1) (b (Var k d))
          get_aT d (BitM f t)   = let faT = get_aT d f
                                      taT = get_aT d f
                                  in if eql False d book faT taT 
                                     then faT 
                                     else error $ "conflict:" ++ show term ++ " :: " ++ show faT ++ "\n         " ++ show term ++ " :: " ++ show taT
          get_aT d (All aT bT)  = aT
          get_aT d t = error $ "undefined get_aT " ++ show d ++ " " ++ show t
      Done (f_typ, f_ctrs, idx1) ->
        -- trace ("failed infer constraints APP 1: " ++ show term ++ " :: " ++ show f_typ) $
        Fail $ CantInfer span (normalCtx book ctx) Nothing
      Fail e -> 
        -- trace ("failed infer constraints APP 2: " ++ show term ++ "error: " ++ show e) $ 
        Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(Sub x) idx = 
  do
  inferWithConstraints d span book ctx x idx
inferWithConstraints d span book ctx term@(Let k (Just t) v f) idx = 
  do
  (tT, t_cnstr, idx1) <- inferWithConstraints d span book ctx t idx
  (vT, v_cnstr, idx2) <- inferWithConstraints d span book ctx v idx1
  let new_ctx = extend ctx k (Var k d) t
  (fT, f_cnstr, idx3) <- inferWithConstraints (d+1) span book new_ctx (f (Var k d)) idx2
  return (fT, [Constr tT Set, Constr vT t] ++ t_cnstr ++ v_cnstr ++ f_cnstr, idx3)
inferWithConstraints d span book ctx term@(Let k Nothing v f) idx = 
  do
  (vT, v_cnstr, idx1) <- inferWithConstraints d span book ctx v idx
  let new_ctx = extend ctx k (Var k d) vT
  (fT, f_cnstr, idx2) <- inferWithConstraints (d+1) span book new_ctx (f (Var k d)) idx1
  return (fT, v_cnstr ++ f_cnstr, idx2)
inferWithConstraints d span book ctx term@(Use k v f) idx = 
  do
  inferWithConstraints d span book ctx (f v) idx
inferWithConstraints d span book ctx term@(Fix k f) idx = 
  Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(Chk v t) idx = 
  do
  (tT, t_cnstr, idx1) <- inferWithConstraints d span book ctx t idx
  (vT, v_cnstr, idx2) <- inferWithConstraints d span book ctx v idx1
  return (t, [Constr tT Set, Constr vT t] ++ t_cnstr ++ v_cnstr, idx2)
inferWithConstraints d span book ctx term@(Tst x) idx = 
  Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(Set) idx = 
  return (Set, [], idx)
inferWithConstraints d span book ctx term@(Emp) idx = 
  return (Set, [], idx)
inferWithConstraints d span book ctx term@(EmpM) idx = 
  Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(Uni) idx = 
  return (Set, [], idx)
inferWithConstraints d span book ctx term@(One) idx = 
  return (Uni, [], idx)
inferWithConstraints d span book ctx term@(UniM f) idx = 
  do
  (fT, f_cnstr, idx1) <- inferWithConstraints d span book ctx f idx
  return (All Uni (UniM fT), f_cnstr, idx1)
inferWithConstraints d span book ctx term@(BitM f t) idx = 
  do
  (fT, f_cnstr, idx1) <- inferWithConstraints d span book ctx f idx
  (tT, t_cnstr, idx2) <- inferWithConstraints d span book ctx t idx1
  return (All Bit (BitM fT tT), f_cnstr ++ t_cnstr, idx2)
inferWithConstraints d span book ctx term@(Zer) idx = 
  return (Nat, [], idx)
inferWithConstraints d span book ctx term@(NatM z s) idx = 
  do
  (zT, z_cnstr, idx1) <- inferWithConstraints d span book ctx z idx
  case cut s of
    Lam p mtp bp -> do
      let new_ctx = extend ctx p (Var p d) Nat
      (sT, s_cnstr, idx2) <- inferWithConstraints (d+1) span book new_ctx (bp (Var p d)) idx1
      return (All Nat (NatM zT (Lam p (Just Nat) (\_ -> sT))), z_cnstr ++ s_cnstr, idx2)
    _ -> do
      (sT, s_cnstr, idx2) <- inferWithConstraints d span book ctx s idx1
      return (All Nat (NatM zT sT), z_cnstr ++ s_cnstr, idx2)
inferWithConstraints d span book ctx term@(Lst t) idx = 
  do
  (tT, t_cnstr, idx1) <- inferWithConstraints d span book ctx t idx
  return (Set, [Constr tT Set] ++ t_cnstr, idx1)
inferWithConstraints d span book ctx term@(Nil) idx = 
  Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(Con h t) idx = 
  do
  (hT, h_cnstr, idx1) <- inferWithConstraints d span book ctx h idx
  (tT, t_cnstr, idx2) <- inferWithConstraints d span book ctx t idx1
  return (Lst hT, [Constr tT (Lst hT)] ++ h_cnstr ++ t_cnstr, idx2)
inferWithConstraints d span book ctx term@(LstM n c) idx = 
  Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(Enu s) idx = 
  return (Set, [], idx)
inferWithConstraints d span book@(Book defs names) ctx term@(Sym s) idx = 
  do
  let bookEnums = [ Enu tags | (k, (_, (Sig (Enu tags) _), Set)) <- M.toList defs ]
  case find isEnuWithTag bookEnums of
    Just t  -> return (t, [], idx)
    Nothing -> Fail $ Undefined span (normalCtx book ctx) ("@" ++ s) Nothing
  where
    isEnuWithTag (Enu tags) = s `elem` tags
    isEnuWithTag _ = False
inferWithConstraints d span book ctx term@(EnuM cs e) idx = 
  Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(Sig a b) idx = 
  do
  (aT, a_cnstr, idx1) <- inferWithConstraints d span book ctx a idx
  (bT, b_cnstr, idx2) <- inferWithConstraints d span book ctx b idx1
  return (Set, [Constr aT Set, Constr bT (All a (Lam "_" Nothing (\_ -> Set)))] ++ a_cnstr ++ b_cnstr, idx2)
inferWithConstraints d span book@(Book defs names) ctx term@(Tup (cut -> Sym s) b) idx = 
  do
  let candidates = [ t | (k, (_, t@(Sig (Enu tags) _), Set)) <- M.toList defs, s `elem` tags ]
  case candidates of
    [t] -> do
      (tT, t_cnstr, idx1) <- inferWithConstraints d span book ctx t idx
      (termT, term_cnstr, idx2) <- inferWithConstraints d span book ctx term idx1
      return (t, [Constr tT Set, Constr termT t] ++ t_cnstr ++ term_cnstr, idx2)
    _ -> Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(Tup a b) idx = 
  Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(SigM f) idx = 
  Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(All a b) idx = 
  do
  (aT, a_cnstr, idx1) <- inferWithConstraints d span book ctx a idx
  (bT, b_cnstr, idx2) <- inferWithConstraints d span book ctx b idx1
  return (Set, [Constr aT Set, Constr bT (All a (Lam "_" Nothing (\_ -> Set)))] ++ a_cnstr ++ b_cnstr, idx2)
inferWithConstraints d span book ctx term@(Eql t a b) idx = 
  do
  (tT, t_cnstr, idx1) <- inferWithConstraints d span book ctx t idx
  (aT, a_cnstr, idx2) <- inferWithConstraints d span book ctx a idx1
  (bT, b_cnstr, idx3) <- inferWithConstraints d span book ctx b idx2
  return (Set, [Constr tT Set, Constr aT t, Constr bT t] ++ t_cnstr ++ a_cnstr ++ b_cnstr, idx3)
inferWithConstraints d span book ctx term@(Rfl) idx = 
  Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(EqlM f) idx = 
  Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(Rwt e f) idx = 
  do
  (eT, e_cnstr, idx1) <- inferWithConstraints d span book ctx e idx
  case force book eT of
    Eql t a b -> do
      let rewrittenCtx = rewriteCtx d book a b ctx
      (fT, f_cnstr, idx2) <- inferWithConstraints d span book rewrittenCtx f idx1
      return (fT, e_cnstr ++ f_cnstr, idx2)
    _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0))) (normal book eT) Nothing
inferWithConstraints d span book ctx term@(Era) idx = 
  Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(Sup l a b) idx = 
  Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(SupM l f) idx = 
  Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(Frk l a b) idx = 
  Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(Met n t c) idx = 
  Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(Num t) idx = 
  return (Set, [], idx)
inferWithConstraints d span book ctx term@(Val (U64_V v)) idx = 
  return (Num U64_T, [], idx)
inferWithConstraints d span book ctx term@(Val (I64_V v)) idx = 
  return (Num I64_T, [], idx)
inferWithConstraints d span book ctx term@(Val (F64_V v)) idx = 
  return (Num F64_T, [], idx)
inferWithConstraints d span book ctx term@(Val (CHR_V v)) idx = 
  return (Num CHR_T, [], idx)
inferWithConstraints d span book ctx term@(Op2 op a b) idx = 
  do
  (aT, a_cnstr, idx1) <- inferWithConstraints d span book ctx a idx
  (bT, b_cnstr, idx2) <- inferWithConstraints d span book ctx b idx1
  case inferOp2Type d span book ctx op aT bT of
    Done resultType -> return (resultType, a_cnstr ++ b_cnstr, idx2)
    Fail e -> Fail e
inferWithConstraints d span book ctx term@(Op1 op a) idx = 
  do
  (aT, a_cnstr, idx1) <- inferWithConstraints d span book ctx a idx
  case inferOp1Type d span book ctx op aT of
    Done resultType -> return (resultType, a_cnstr, idx1)
    Fail e -> Fail e
inferWithConstraints d span book ctx term@(Pri U64_TO_CHAR) idx = 
  return (All (Num U64_T) (Lam "x" Nothing (\_ -> Num CHR_T)), [], idx)
inferWithConstraints d span book ctx term@(Pri CHAR_TO_U64) idx = 
  return (All (Num CHR_T) (Lam "x" Nothing (\_ -> Num U64_T)), [], idx)
inferWithConstraints d span book ctx term@(Pri HVM_INC) idx = 
  Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(Pri HVM_DEC) idx = 
  Fail $ CantInfer span (normalCtx book ctx) Nothing
inferWithConstraints d span book ctx term@(Log s x) idx = 
  do
  (sT, s_cnstr, idx1) <- inferWithConstraints d span book ctx s idx
  (xT, x_cnstr, idx2) <- inferWithConstraints d span book ctx x idx1
  return (xT, [Constr sT (Lst (Num CHR_T))] ++ s_cnstr ++ x_cnstr, idx2)
inferWithConstraints d span book ctx term@(IO t) idx = 
  do
  (tT, t_cnstr, idx1) <- inferWithConstraints d span book ctx t idx
  return (Set, [Constr tT Set] ++ t_cnstr, idx1)
inferWithConstraints d span book ctx term@(Pri IO_PURE) idx = 
  return (All Set (Lam "A" (Just Set) (\a ->
    All a (Lam "x" (Just a) (\_ -> IO a)))), [], idx)
inferWithConstraints d span book ctx term@(Pri IO_BIND) idx = 
  return (All Set (Lam "A" (Just Set) (\a ->
    All Set (Lam "B" (Just Set) (\b ->
      All (IO a) (Lam "m" (Just (IO a)) (\_ ->
        All (All a (Lam "_" (Just a) (\_ -> IO b))) (Lam "f" Nothing (\_ ->
          IO b)))))))), [], idx)
inferWithConstraints d span book ctx term@(Pri IO_PRINT) idx = 
  return (All (Lst (Num CHR_T)) (Lam "s" Nothing (\_ -> IO Uni)), [], idx)
inferWithConstraints d span book ctx term@(Pri IO_PUTC) idx = 
  return (All (Num CHR_T) (Lam "c" Nothing (\_ -> IO Uni)), [], idx)
inferWithConstraints d span book ctx term@(Pri IO_GETC) idx = 
  return (IO (Num CHR_T), [], idx)
inferWithConstraints d span book ctx term@(Pri IO_READ_FILE) idx = 
  return (All (Lst (Num CHR_T)) (Lam "path" Nothing (\_ -> IO (Lst (Num CHR_T)))), [], idx)
inferWithConstraints d span book ctx term@(Pri IO_WRITE_FILE) idx = 
  return (All (Lst (Num CHR_T)) (Lam "path" Nothing (\_ ->
    All (Lst (Num CHR_T)) (Lam "content" Nothing (\_ ->
      IO Uni)))), [], idx)
inferWithConstraints d span book ctx term@(Pat p s b) idx = 
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
    (All a b, Set) -> do
      a' <- check d span book ctx a Set
      b' <- check d span book ctx b (All a (Lam "_" Nothing (\_ -> Set)))
      return $ All a' b'

    (Chk x t, _) | equal d book t nGoal -> do
      _ <- check d span book ctx t Set
      check d span book ctx x t
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
          t <- case infer d span book ctx v Nothing of
            Done t -> return t
            -- _      -> infer (d+1) span book ctx (Var k d) (Just (f (Var k d)))
            _      -> inferVarInEnv d span book ctx k f
          -- t' <- reduceEtas d span <$> check d span book ctx t Set
          t' <- check d span book ctx (reduceEtas d span t) Set
          -- traceM $ "CHECKED THAT 1 " ++ show t ++ " -> " ++ show t' ++ " :: " ++ show Set
          -- traceM $ "WILL CHECK IF 1 " ++ show v ++ " :: " ++ show t'
          v' <- cutChk <$> check d span book ctx v t'
          -- traceM $ "CHECKED THAT 2 " ++ show v ++ " -> " ++ show v' ++ " :: " ++ show t'
          f' <- check (d+1) span book (extend ctx k (Var k d) t') (f (Var k d)) goal
          -- traceM $ "CHECKED THAT 3 " ++ show (f (Var k d)) ++ " -> " ++ show v' ++ " :: " ++ show goal
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
      -- return $ Lam k t (\v -> bindVarByIndex d v f')
      return $ Lam k (Just $ reduceEtas d span a) (\v -> bindVarByIndex d v f')

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

    (App fn@(cut -> BitM f t) x, _) -> 
      -- trace ("APP BITM: " ++ show term ++ " :: " ++ show goal) $ 
      do
      let fn_name = "$aux_"++show d
      x'    <- check d span book ctx x Bit
      goal' <- check d span book ctx goal Set
      res <- check d span book ctx (Let fn_name (Just (All Bit (Lam "_" Nothing (\_ -> goal')))) fn (\v -> App v x')) goal
      return 
        -- $ trace ("checked that " ++ show term ++ " -> " ++ show res) $ 
        res
    
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
    -- trace ("-verify: " ++ show term ++ " :: " ++ show t ++ " == " ++ show goal) $
    equal d book t goal
    then do 
    -- trace ("-verify TRUE: " ++ show term ++ " :: " ++ show t ++ " == " ++ show goal) $
      -- return term
      case term of
        -- Lam k mt b -> return $ Chk (Lam k mt b) t
        _ -> return term
    else 
    -- trace ("-verify FALSE: " ++ show term ++ " :: " ++ show t ++ " == " ++ show goal ++ " ||||||||| " ++ show (equal d book t goal)) $
      Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book t) Nothing

