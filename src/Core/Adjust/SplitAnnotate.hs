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

module Core.Adjust.SplitAnnotate where

import Control.Monad (unless, when, foldM)
import Control.Monad.Except
import Control.Monad.State
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
import Core.LongEqual
import Core.FreeVars
import Core.Rewrite
import Core.WHNF
import Core.Adjust.ReduceEtas

-- Utils
-- -------

extend :: Ctx -> Name -> Term -> Term -> Ctx
extend (Ctx ctx) k v t = Ctx (ctx ++ [(k, v, t)])

-- Get span for the left operand of a binary operation by estimating from the operator span
getLeftOperandSpan :: Span -> Span
getLeftOperandSpan opSpan =
  let (begLine, begCol) = spanBeg opSpan
      (endLine, endCol) = spanEnd opSpan
      src = spanSrc opSpan
      pth = spanPth opSpan
  in if begLine == endLine
     then
       -- Try to find the '+' operator and end the span just before it
       let line = lines src !! (begLine - 1)
           beforeCol = take (endCol - 1) line
           -- Find the last '+' in the span and end just before it
           plusPos = case reverse $ zip [1..] beforeCol of
             [] -> begCol
             positions -> case [(pos, c) | (pos, c) <- positions, c == '+'] of
               [] -> begCol  -- No + found, use beginning
               ((pos, _):_) -> pos - 1  -- End just before the +
       in Span (begLine, begCol) (begLine, max begCol plusPos) pth src
     else opSpan  -- Multi-line, just use original span

-- Check if a type is valid for binary operations (more precise than canOp2)
isValidForOp2 :: Term -> Bool
isValidForOp2 typ = case typ of
  Num _ -> True
  Nat   -> True
  Bit   -> True
  All _ _ -> False  -- Function types are not valid for binary operations
  _     -> False

-- Check if a Sigma type represents a constructor
-- Constructor types are sigma lists that:
-- 1. Start with an Enum (constructor tag)
-- 2. End with Unit (by convention)
isConstructorSigma :: Book -> Term -> Bool
isConstructorSigma book (Sig a b) = case force book a of
  Enu _ -> endsWithUnit b 0
  _     -> False
  where
    -- Check if the sigma chain ends with Unit (type or value)
    endsWithUnit :: Term -> Int -> Bool
    endsWithUnit _ depth | depth > 10 = False -- Prevent infinite recursion
    endsWithUnit (Lam _ _ f) d = endsWithUnit (f (Var "_" 0)) (d+1)
    endsWithUnit (App f _) d = endsWithUnit f (d+1)
    endsWithUnit Uni _ = True  -- Unit type
    endsWithUnit One _ = True  -- Unit value ()
    endsWithUnit (Sig _ b') d = endsWithUnit b' (d+1)
    -- Handle EnuM (enum match) - check all branches
    endsWithUnit (EnuM cases df) d = 
      all (\(_, branch) -> endsWithUnit branch (d+1)) cases &&
      case df of
        Lam _ _ f -> endsWithUnit (f (Var "_" 0)) (d+1)
        _ -> endsWithUnit df (d+1)
    -- Handle Use expressions
    endsWithUnit (Use _ _ f) d = endsWithUnit (f (Var "_" 0)) (d+1)
    endsWithUnit _ _ = False
isConstructorSigma _ _ = False

-- Type Checker
-- ------------

-- -- Apply constraints to solve metavariables
-- applyConstraints :: Int -> Span -> Book -> Ctx -> [Constraint] -> Term -> Int -> Result (Term, [Constraint])
-- applyConstraints d span book ctx constraints term idx = case constraints of
--   -- Base case: no more constraints
--   [] -> return (term, [])
--
--   -- Metavariable on left side
--   (Constr (Var k@('?':_) i) val) : rest -> do
--     -- Substitute metavariable with its value
--     term' <- substInTerm i val term
--     rest' <- substInConstraints i val rest
--     applyConstraints d span book ctx rest' term' idx
--
--   -- Metavariable on right side
--   (Constr val (Var k@('?':_) i)) : rest -> do
--     -- Substitute metavariable with its value
--     term' <- substInTerm i val term
--     rest' <- substInConstraints i val rest
--     applyConstraints d span book ctx rest' term' idx
--
--   -- Let on either side: beta reduce
--   (Constr (Let k t v b) val) : rest ->
--     applyConstraints d span book ctx (Constr (b v) val : rest) term idx
--
--   (Constr val (Let k t v b)) : rest ->
--     applyConstraints d span book ctx (Constr val (b v) : rest) term idx
--
--   -- Structural decomposition: All types
--   (Constr (All a b) (All a' b')) : rest ->
--     applyConstraints d span book ctx (Constr a a' : Constr b b' : rest) term idx
--
--   -- Structural decomposition: Applications
--   (Constr (App f x) (App f' x')) : rest ->
--     applyConstraints d span book ctx (Constr f f' : Constr x x' : rest) term idx
--
--   -- Structural decomposition: Lambdas
--   (Constr (Lam k1 mt1 b1) (Lam k2 mt2 b2)) : rest ->
--     applyConstraints (d+1) span book ctx 
--       (Constr (b1 (Var k1 d)) (b2 (Var k2 d)) : rest) 
--       term (idx-1)
--
--   -- Beta reduction when application meets lambda
--   (Constr a (App (Lam _ _ b) x)) : rest ->
--     applyConstraints d span book ctx (Constr a (b x) : rest) term idx
--
--   (Constr (App (Lam _ _ b) x) a) : rest ->
--     applyConstraints d span book ctx (Constr (b x) a : rest) term idx
--
--   -- Already equal: skip constraint
--   (Constr a b) : rest | equal d book a b ->
--     applyConstraints d span book ctx rest term idx
--
--   -- Pattern matching constructs decomposition
--   -- NatM
--   (Constr (NatM z1 s1) (NatM z2 s2)) : rest ->
--     applyConstraints d span book ctx (Constr z1 z2 : Constr s1 s2 : rest) term idx
--
--   -- BitM  
--   (Constr (BitM f1 t1) (BitM f2 t2)) : rest ->
--     applyConstraints d span book ctx (Constr f1 f2 : Constr t1 t2 : rest) term idx
--
--   -- UniM
--   (Constr (UniM f1) (UniM f2)) : rest ->
--     applyConstraints d span book ctx (Constr f1 f2 : rest) term idx
--
--   -- LstM
--   (Constr (LstM n1 c1) (LstM n2 c2)) : rest ->
--     applyConstraints d span book ctx (Constr n1 n2 : Constr c1 c2 : rest) term idx
--
--   -- EnuM
--   (Constr (EnuM cs1 df1) (EnuM cs2 df2)) : rest | map fst cs1 == map fst cs2 -> do
--     let caseConstraints = zipWith (\(_, t1) (_, t2) -> Constr t1 t2) cs1 cs2
--     applyConstraints d span book ctx (caseConstraints ++ [Constr df1 df2] ++ rest) term idx
--
--   -- SigM
--   (Constr (SigM f1) (SigM f2)) : rest ->
--     applyConstraints d span book ctx (Constr f1 f2 : rest) term idx
--
--   -- SupM
--   (Constr (SupM l1 f1) (SupM l2 f2)) : rest ->
--     applyConstraints d span book ctx (Constr l1 l2 : Constr f1 f2 : rest) term idx
--
--   -- Value types
--   (Constr (Sig a1 b1) (Sig a2 b2)) : rest ->
--     applyConstraints d span book ctx (Constr a1 a2 : Constr b1 b2 : rest) term idx
--
--   (Constr (Tup a1 b1) (Tup a2 b2)) : rest ->
--     applyConstraints d span book ctx (Constr a1 a2 : Constr b1 b2 : rest) term idx
--
--   (Constr (Eql t1 a1 b1) (Eql t2 a2 b2)) : rest ->
--     applyConstraints d span book ctx 
--       (Constr t1 t2 : Constr a1 a2 : Constr b1 b2 : rest) term idx
--
--   (Constr (Lst t1) (Lst t2)) : rest ->
--     applyConstraints d span book ctx (Constr t1 t2 : rest) term idx
--
--   (Constr (IO t1) (IO t2)) : rest ->
--     applyConstraints d span book ctx (Constr t1 t2 : rest) term idx
--
--   (Constr (Num t1) (Num t2)) : rest | t1 == t2 ->
--     applyConstraints d span book ctx rest term idx
--
--   -- Default: unsolvable constraint
--   (Constr a b) : rest ->
--     Fail $ CantInfer span (normalCtx book ctx) 
--       (Just $ "Unsolvable constraint: " ++ show a ++ " == " ++ show b)
--
--   where
--     -- Helper functions for substitution
--     substInTerm :: Int -> Term -> Term -> Result Term
--     substInTerm i val term = return $ bindVarByIndex i val term
--
--     substInConstraint :: Int -> Term -> Constraint -> Constraint
--     substInConstraint i val (Constr a b) = 
--       Constr (bindVarByIndex i val a) (bindVarByIndex i val b)
--
--     substInConstraints :: Int -> Term -> [Constraint] -> Result [Constraint]
--     substInConstraints i val constraints = 
--       return $ map (substInConstraint i val) constraints


-- Constraint (from your code)
data Constraint = Constr Term Term
  -- deriving Show
instance Show Constraint where
  show (Constr t1 t2) = "Constraint: " ++ show t1 ++ " === " ++ show t2

-- Substitution maps metavariable names to terms
type Subst = M.Map String Term

data TypeState = TypeState
  { constraints :: [Constraint]  -- Accumulated constraints
  , subst :: Subst              -- Current substitutions
  , nextIdx :: Int               -- For generating fresh metavariables
  , gatherOnly :: Bool
  }

type TypeM = ExceptT Error (State TypeState)

-- Add constraint
addConstraint :: Constraint -> TypeM ()
addConstraint c = modify $ \s -> s { constraints = c : constraints s }

-- Generate fresh metavariable
freshMeta :: String -> TypeM Term
freshMeta prefix = do
  idx <- gets nextIdx
  modify $ \s -> s { nextIdx = idx - 1 }
  return $ Var ("?" ++ prefix ++ show idx) idx

-- Add substitution
addSubst :: String -> Term -> TypeM ()
addSubst k t = modify $ \s -> s { subst = M.insert k t (subst s) }

-- Occurs check
occursCheck :: Span -> Book -> Ctx -> String -> Term -> TypeM ()
occursCheck span book ctx k t =
  when (k `S.member` freeVars S.empty t) $
    throwError $ CantInfer span (normalCtx book ctx)
      (Just $ "Occurs check failed: " ++ k ++ " in " ++ show (normal book t))

solveConstraints :: Int -> Span -> Book -> Ctx -> TypeM ()
solveConstraints d span book ctx = do
  cs <- gets constraints
  mapM_ solveOne cs
  where
    solveOne (Constr t1 t2) = do
      s <- gets subst
      t1' <- applySubst d s t1
      t2' <- applySubst d s t2
      unifyTerm d span book ctx t1' t2'

-- Add this after your other helper functions
softFail :: Span -> Book -> Ctx -> Maybe String -> TypeM Term
softFail span book ctx msg = do
  gathering <- gets gatherOnly
  if gathering
    then freshMeta "unknown"
    else throwError (CantInfer span (normalCtx book ctx) msg)

-- Unify two terms, updating the substitution map
unifyTerm :: Int -> Span -> Book -> Ctx -> Term -> Term -> TypeM ()
unifyTerm d span book ctx t1 t2 = case (force book t1, force book t2) of
  -- Base case: equal terms
  (t1', t2') | equal 0 book t1' t2' -> return ()
  -- Metavariable cases
  (Var k@('?':_) i, t) | not (k `S.member` freeVars S.empty t) -> do
    occursCheck span book ctx k t
    addSubst k t
  (t, Var k@('?':_) i) | not (k `S.member` freeVars S.empty t) -> do
    occursCheck span book ctx k t
    addSubst k t
  -- Structural decomposition
  (All a1 b1, All a2 b2) -> do
    unifyTerm d span book ctx a1 a2
    x <- freshMeta "x"
    unifyTerm d span book ctx (App b1 x) (App b2 x)
  (App f1 x1, App f2 x2) -> do
    unifyTerm d span book ctx f1 f2
    unifyTerm d span book ctx x1 x2
  -- Placeholder for complex cases (e.g., App ?k x ≡ t)
  _ -> throwError $ CantInfer span (normalCtx book ctx)
    (Just $ "Unsolvable constraint: " ++ show t1 ++ " == " ++ show t2)

applySubst :: Int -> Subst -> Term -> TypeM Term
applySubst d subst term = case term of
  Var k@('?':_) i -> case (M.lookup k subst) of
    Just term' -> 
      -- trace (show term ++ " -> " ++ show term' ++ " || under " ++ show subst) $ 
      applySubst d subst term'
    Nothing    -> 
      -- trace (show term ++ " -> " ++ show term ++ " || under " ++ show subst) $ 
      return term
  Var k i -> return term
  Ref k i -> return term
  Sub t -> Sub <$> applySubst d subst t
  Fix k b -> do
    b' <- applySubst (d+1) subst (b (Var k d))
    return $ Fix k (\v -> bindVarByIndex d v b')
  Let k mt v b -> do
    mt' <- traverse (applySubst d subst) mt
    v' <- applySubst d subst v
    b' <- applySubst (d+1) subst (b (Var k d))
    return $ Let k mt' v' (\v -> bindVarByIndex d v b')
  Use k v b -> do
    v' <- applySubst d subst v
    b' <- applySubst (d+1) subst (b (Var k d))
    return $ Use k v' (\v -> bindVarByIndex d v b')
  Chk x t -> Chk <$> applySubst d subst x <*> applySubst d subst t
  Tst x -> Tst <$> applySubst d subst x
  Set -> return term
  Emp  -> return term
  EmpM -> return term
  Uni -> return term
  One -> return term
  UniM f -> UniM <$> applySubst d subst f
  Bit -> return term
  Bt0 -> return term
  Bt1 -> return term
  BitM f t -> BitM <$> applySubst d subst f <*> applySubst d subst t
  Nat -> return term
  Zer -> return term
  Suc n -> Suc <$> applySubst d subst n
  NatM z s -> NatM <$> applySubst d subst z <*> applySubst d subst s
  Lst t -> Lst <$> applySubst d subst t
  Nil -> return term
  Con h t -> Con <$> applySubst d subst h <*> applySubst d subst t
  LstM n c -> LstM <$> applySubst d subst n <*> applySubst d subst c
  Enu s -> return term
  Sym s -> return term
  EnuM cs d' -> EnuM <$> mapM (\(s, t) -> (s,) <$> applySubst d subst t) cs <*> applySubst d subst d'
  Num nt -> return term
  Val nv -> return term
  Op2 op a b -> Op2 op <$> applySubst d subst a <*> applySubst d subst b
  Op1 op a -> Op1 op <$> applySubst d subst a
  Sig a b -> do
    a' <- applySubst d subst a
    b' <- applySubst d subst b
    return $ Sig a' b'
  Tup a b -> Tup <$> applySubst d subst a <*> applySubst d subst b
  SigM f -> SigM <$> applySubst d subst f
  All a b -> do
    a' <- applySubst d subst a
    b' <- applySubst d subst b
    return $
      -- trace (show (All a b) ++ " -> " ++ show (All a' b') ++ " under " ++ show subst) $ 
      All a' b'
  Lam k mt b -> do
    mt' <- traverse (applySubst d subst) mt
    b'  <- applySubst (d+1) subst (b (Var k d))
    return $ Lam k mt' (\v -> bindVarByIndex d v b')
  App f x -> App <$> applySubst d subst f <*> applySubst d subst x
  Eql t a b -> Eql <$> applySubst d subst t <*> applySubst d subst a <*> applySubst d subst b
  Rfl -> return term
  EqlM f -> EqlM <$> applySubst d subst f
  Rwt e f -> Rwt <$> applySubst d subst e <*> applySubst d subst f
  Met n t ctx -> Met n <$> applySubst d subst t <*> mapM (applySubst d subst) ctx
  Era -> return term
  Sup l a b -> Sup <$> applySubst d subst l <*> applySubst d subst a <*> applySubst d subst b
  SupM l f -> SupM <$> applySubst d subst l <*> applySubst d subst f
  Loc l t -> Loc l <$> applySubst d subst t
  Log s x -> Log <$> applySubst d subst s <*> applySubst d subst x
  Pri pf -> return term
  Pat ts ms cs -> Pat
    <$> mapM (applySubst d subst) ts
    <*> mapM (\(s, t) -> (s,) <$> applySubst d subst t) ms
    <*> mapM (\(ps, t) -> (,) <$> mapM (applySubst d subst) ps <*> applySubst d subst t) cs
  Frk l a b -> Frk <$> applySubst d subst l <*> applySubst d subst a <*> applySubst d subst b
  IO t -> IO <$> applySubst d subst t

inferLetVarType :: Int -> Span -> Book -> Ctx -> Term -> (Term -> Term) -> Result Term
inferLetVarType d span book ctx v f = 
  case runState (runExceptT computation) initialState of
    (Left err, _) -> Fail err
    (Right t, _) -> Done t
  where
    initialState = TypeState [] M.empty (-1) False
    computation = do
      vMeta <- freshMeta "vartype"
      let new_ctx = extend ctx "tmp" (Var "tmp" d) vMeta
      
      -- Set gathering mode for body exploration
      modify (\s -> s { gatherOnly = True })
      _ <- inferGo (d+1) span book new_ctx (f (Var "tmp" d))
      modify (\s -> s { gatherOnly = False })
      
      -- Try to infer v normally (non-gathering mode)
      vT <- inferGo d span book ctx v
      addConstraint (Constr vT vMeta)
      
      solveConstraints d span book ctx
      s <- gets subst
      applySubst d s vMeta

-- -- Main inference function that will apply constraints at the end
infer :: Int -> Span -> Book -> Ctx -> Term -> Result Term
infer d span book ctx term = 
  case runState (runExceptT computation) initialState of
    (Left err, _) -> Fail err
    (Right t, _)  -> Done t
  where
    initialState = TypeState [] M.empty (-1) False
    computation = do
      typeWithMetas <- inferGo d span book ctx term
      solveConstraints d span book ctx
      s <- gets subst
      finalType <- applySubst d s typeWithMetas
      if any (\case ('?':_) -> True; _ -> False) (S.toList (freeVars S.empty finalType))
        then throwError $ CantInfer span (normalCtx book ctx) (Just "Unresolved metavariables remain")
        else 
            -- trace ("-infered: " ++ show term ++ " :: " ++ show finalType) $ 
            return finalType

-- The core inference that generates constraints
inferGo :: Int -> Span -> Book -> Ctx -> Term -> TypeM Term
inferGo d span book@(Book defs names) ctx term = case term of

  -- Variables - hard error, must be in context
  Var k i -> do
    let Ctx ks = ctx
    if i < length ks && i >= 0
      then let (_, _, typ) = ks !! i in return typ
      else throwError (CantInfer span (normalCtx book ctx) Nothing)

  -- References - hard error if undefined
  Ref k i -> case getDefn book k of
    Just (_, _, typ) -> return typ
    Nothing -> throwError (Undefined span (normalCtx book ctx) k Nothing)

  -- Sub
  Sub x -> inferGo d span book ctx x

  -- Let with type annotation
  Let k (Just t) v f -> do
    tT <- inferGo d span book ctx t
    addConstraint (Constr tT Set)
    vT <- inferGo d span book ctx v
    addConstraint (Constr vT t)
    let new_ctx = extend ctx k (Var k d) t
    inferGo (d+1) span book new_ctx (f (Var k d))

  -- Let without type annotation
  Let k Nothing v f -> do
    vT <- inferGo d span book ctx v
    let new_ctx = extend ctx k (Var k d) vT
    inferGo (d+1) span book new_ctx (f (Var k d))

  -- Use
  Use k v f -> inferGo d span book ctx (f v)

  -- Fix - soft fail
  Fix k f -> softFail span book ctx Nothing

  -- Check annotation
  Chk v t -> do
    tT <- inferGo d span book ctx t
    addConstraint (Constr tT Set)
    vT <- inferGo d span book ctx v
    addConstraint (Constr vT t)
    return t

  -- Trust - soft fail
  Tst _ -> softFail span book ctx Nothing

  -- Set
  Set -> return Set

  -- Empty type
  Emp -> return Set

  -- Empty eliminator - soft fail
  EmpM -> softFail span book ctx Nothing

  -- Unit type
  Uni -> return Set

  -- Unit value
  One -> return Uni

  -- Unit eliminator - soft fail
  UniM f -> softFail span book ctx Nothing

  -- Bool type
  Bit -> return Set

  -- Bool false
  Bt0 -> return Bit

  -- Bool true
  Bt1 -> return Bit

  -- Bool eliminator - soft fail
  BitM f t -> softFail span book ctx Nothing

  -- Nat type
  Nat -> return Set

  -- Nat zero
  Zer -> return Nat

  -- Nat successor
  Suc n -> do
    nT <- inferGo d span book ctx n
    addConstraint (Constr nT Nat)
    return Nat

  -- Nat eliminator - soft fail
  NatM z s -> softFail span book ctx Nothing

  -- IO type
  IO t -> do
    tT <- inferGo d span book ctx t
    addConstraint (Constr tT Set)
    return Set

  -- List type
  Lst t -> do
    tT <- inferGo d span book ctx t
    addConstraint (Constr tT Set)
    return Set

  -- List nil - soft fail but we know it's a list
  Nil -> do
    elemType <- freshMeta "elem"
    return (Lst elemType)

  -- List cons - soft fail but gather constraints
  Con h t -> do
    hT <- inferGo d span book ctx h
    tT <- inferGo d span book ctx t
    case force book tT of
      Lst elemT -> do
        addConstraint (Constr hT elemT)
        return tT
      _ -> do
        elemType <- freshMeta "elem"
        addConstraint (Constr tT (Lst elemType))
        addConstraint (Constr hT elemType)
        return (Lst elemType)

  -- List eliminator - soft fail
  LstM n c -> softFail span book ctx Nothing

  -- Enum type
  Enu s -> return Set

  -- Enum symbol
  Sym s -> do
    let bookEnums = [ Enu tags | (k, (_, (Sig (Enu tags) _), Set)) <- M.toList defs ]
    case find isEnuWithTag bookEnums of
      Just t -> return t
      Nothing -> throwError (Undefined span (normalCtx book ctx) ("@" ++ s) Nothing)
    where
      isEnuWithTag (Enu tags) = s `elem` tags
      isEnuWithTag _ = False

  -- Enum eliminator
  EnuM cs e -> do
    if not (null cs)
      then do
        -- Get the domain type by inferring the type of the first case's tag
        let firstTag = fst (head cs)
        domainType <- inferGo d span book ctx (Sym firstTag)
        
        -- Check if all cases are covered
        case domainType of
          Enu syms -> do
            let covered_syms = map fst cs
            let all_covered = length covered_syms >= length syms 
                           && all (`elem` syms) covered_syms
            
            -- Infer types from all branches
            branchTypes <- mapM (inferGo d span book ctx . snd) cs
            
            -- Determine the return type
            returnType <- if all_covered
              then do
                -- All cases covered, ignore default (it's just filler)
                case branchTypes of
                  (t:rest) -> do
                    -- Add constraints that all branches have same type
                    mapM_ (\bt -> addConstraint (Constr bt t)) rest
                    return t
                  [] -> freshMeta "enum_ret"  -- Shouldn't happen
              else do
                -- Not all covered, need to check default too
                defaultType <- inferGo d span book ctx e
                case branchTypes of
                  (t:rest) -> do
                    -- All branches and default should have same return type
                    mapM_ (\bt -> addConstraint (Constr bt t)) rest
                    -- Default should be a function from enum to return type
                    addConstraint (Constr defaultType (All domainType (Lam "_" Nothing (\_ -> t))))
                    return t
                  [] -> do
                    -- Only default, extract return type from it
                    retMeta <- freshMeta "enum_ret"
                    addConstraint (Constr defaultType (All domainType (Lam "_" Nothing (\_ -> retMeta))))
                    return retMeta
            
            -- Return the eliminator type: Enum -> ReturnType
            return (All domainType (Lam "_" Nothing (\_ -> returnType)))
            
          _ -> do
            -- Domain type is not a concrete enum, might be a metavariable
            -- Still try to gather constraints
            branchTypes <- mapM (inferGo d span book ctx . snd) cs
            defaultType <- inferGo d span book ctx e
            returnType <- case branchTypes of
              (t:rest) -> do
                mapM_ (\bt -> addConstraint (Constr bt t)) rest
                return t
              [] -> freshMeta "enum_ret"
            addConstraint (Constr defaultType (All domainType (Lam "_" Nothing (\_ -> returnType))))
            return (All domainType (Lam "_" Nothing (\_ -> returnType)))
      else 
        -- No cases at all
        softFail span book ctx Nothing

  -- Sigma type
  Sig a b -> do
    aT <- inferGo d span book ctx a
    addConstraint (Constr aT Set)
    bT <- inferGo d span book ctx b
    addConstraint (Constr bT (All a (Lam "_" Nothing (\_ -> Set))))
    return Set

  -- Tuple
  Tup a b -> do
    aT <- inferGo d span book ctx a
    bT <- inferGo d span book ctx b
    return (Sig aT (Lam "_" Nothing (\_ -> bT)))

  -- Sigma eliminator - soft fail
  SigM f -> softFail span book ctx Nothing

  -- Pi type
  All a b -> do
    aT <- inferGo d span book ctx a
    addConstraint (Constr aT Set)
    bT <- inferGo d span book ctx b
    addConstraint (Constr bT (All a (Lam "_" Nothing (\_ -> Set))))
    return Set

  -- Lambda with type annotation
  Lam k (Just t) body -> do
    tT <- inferGo d span book ctx t
    addConstraint (Constr tT Set)
    let new_ctx = extend ctx k (Var k d) t
    bodyType <- inferGo (d+1) span book new_ctx (body (Var k d))
    return (All t (Lam k (Just t) (\v -> bindVarByIndex d v bodyType)))

  -- Lambda without type annotation
  Lam k Nothing body -> do
    argMeta <- freshMeta k
    let new_ctx = extend ctx k (Var k d) argMeta
    bodyType <- inferGo (d+1) span book new_ctx (body (Var k d))
    return (All argMeta (Lam k Nothing (\v -> bindVarByIndex d v bodyType)))

  -- Application
  App f x -> do
    fT <- inferGo d span book ctx f
    case force book fT of
      All aT bT -> do
        xT <- inferGo d span book ctx x
        addConstraint (Constr xT aT)
        case bT of
          Lam _ _ body -> return (body x)
          _ -> return (App bT x)
      _ -> do
        -- Function type unknown, create metavariables
        xT <- inferGo d span book ctx x
        resultMeta <- freshMeta "result"
        funBodyMeta <- freshMeta "funbody"
        addConstraint (Constr fT (All xT funBodyMeta))
        addConstraint (Constr resultMeta (App funBodyMeta x))
        return resultMeta

  -- Equality type
  Eql t a b -> do
    tT <- inferGo d span book ctx t
    addConstraint (Constr tT Set)
    aT <- inferGo d span book ctx a
    addConstraint (Constr aT t)
    bT <- inferGo d span book ctx b
    addConstraint (Constr bT t)
    return Set

  -- Refl - soft fail
  Rfl -> softFail span book ctx Nothing

  -- Equality eliminator - soft fail
  EqlM f -> softFail span book ctx Nothing

  -- Rewrite
  Rwt e f -> do
    eT <- inferGo d span book ctx e
    case force book eT of
      Eql t a b -> do
        let rewrittenCtx = rewriteCtx d book a b ctx
        inferGo d span book rewrittenCtx f
      _ -> do
        let eqlType = Eql (Var "_" 0) (Var "_" 0) (Var "_" 0)
        throwError (trace "AAAAAAAA" $ TypeMismatch span (normalCtx book ctx) (normal book eqlType) (normal book eT) Nothing)

  -- Location
  Loc l t -> inferGo d l book ctx t

  -- Erasure - soft fail
  Era -> softFail span book ctx Nothing

  -- Sup - soft fail
  Sup l a b -> softFail span book ctx Nothing

  -- Sup eliminator - soft fail
  SupM l f -> softFail span book ctx Nothing

  -- Fork - soft fail
  Frk l a b -> softFail span book ctx Nothing

  -- Met - soft fail
  Met n t c -> softFail span book ctx Nothing

  -- Numeric type
  Num t -> return Set

  -- Numeric values
  Val (U64_V v) -> return (Num U64_T)
  Val (I64_V v) -> return (Num I64_T)
  Val (F64_V v) -> return (Num F64_T)
  Val (CHR_V v) -> return (Num CHR_T)

  -- Binary operations
  Op2 op a b -> do
    aT <- inferGo d span book ctx a
    bT <- inferGo d span book ctx b
    case inferOp2Type d span book ctx op aT bT of
      Done resultType -> return resultType
      Fail e -> throwError e

  -- Unary operations
  Op1 op a -> do
    aT <- inferGo d span book ctx a
    case inferOp1Type d span book ctx op aT of
      Done resultType -> return resultType
      Fail e -> throwError e

  -- Primitives
  Pri U64_TO_CHAR -> return (All (Num U64_T) (Lam "x" Nothing (\_ -> Num CHR_T)))
  Pri CHAR_TO_U64 -> return (All (Num CHR_T) (Lam "x" Nothing (\_ -> Num U64_T)))
  Pri HVM_INC -> softFail span book ctx Nothing
  Pri HVM_DEC -> softFail span book ctx Nothing
  Pri IO_PURE -> do
    let aType = Lam "A" (Just Set) (\a -> All a (Lam "x" (Just a) (\_ -> IO a)))
    return (All Set aType)
  Pri IO_BIND -> do
    let aType = Lam "A" (Just Set) (\a -> 
                  All Set (Lam "B" (Just Set) (\b ->
                    All (IO a) (Lam "m" (Just (IO a)) (\_ ->
                      All (All a (Lam "_" (Just a) (\_ -> IO b))) 
                          (Lam "f" Nothing (\_ -> IO b)))))))
    return (All Set aType)
  Pri IO_PRINT -> return (All (Lst (Num CHR_T)) (Lam "s" Nothing (\_ -> IO Uni)))
  Pri IO_PUTC -> return (All (Num CHR_T) (Lam "c" Nothing (\_ -> IO Uni)))
  Pri IO_GETC -> return (IO (Num CHR_T))
  Pri IO_READ_FILE -> do
    let pathType = Lst (Num CHR_T)
    return (All pathType (Lam "path" Nothing (\_ -> IO pathType)))
  Pri IO_WRITE_FILE -> do
    let strType = Lst (Num CHR_T)
    return (All strType (Lam "path" Nothing (\_ ->
              All strType (Lam "content" Nothing (\_ -> IO Uni)))))

  -- Log
  Log s x -> do
    sT <- inferGo d span book ctx s
    addConstraint (Constr sT (Lst (Num CHR_T)))
    inferGo d span book ctx x

  -- Pattern - hard error, not supported
  Pat _ _ _ -> do
    let nctx = normalCtx book ctx
    let msg = Just "Pat not supported"
    throwError (Unsupported span nctx msg)

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
          -- t <- infer d span book ctx v
          -- vT <- inferLetVarType d span book ctx v f (-1)
          t <- inferLetVarType d span book ctx v f
          t' <- check d span book ctx (reduceEtas d span book t) Set
          v' <- cutChk <$> check d span book ctx v t'
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
      -- return $ Lam k t (\v -> bindVarByIndex d v f')
      return $ Lam k (Just $ reduceEtas d span book a) (\v -> bindVarByIndex d v f')

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
    
    -- (UniM f, All a rT) | longEqual d book a Uni -> do
    --   f' <- check d span book ctx f (App rT One)
    --   -- return $ (Chk (UniM f') (All Uni rT))
    --   return $ UniM f'

    -- Type mismatch for UniM
    (UniM f, _) -> do
      Fail $ trace ("HHHHH " ++ show term ++ " :: " ++ show (force book goal)) $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All Uni (Lam "_" Nothing (\_ -> (Var "?" 0))))) Nothing

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
        else Fail $ trace "BBBBBBB" $ TypeMismatch span (normalCtx book ctx) (normal book (Enu y)) (normal book (Sym s)) Nothing

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
          Fail $ trace "CCCCCCCCCC" $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Enu [h, "..."]) (Lam "_" Nothing (\_ -> (Var "?" 0))))) Nothing

    -- Type mismatch for EnuM
    (EnuM cs df, _) -> do
      Fail $ trace "AAAA" $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Enu []) (Lam "_" Nothing (\_ -> (Var "?" 0))))) Nothing

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
      Fail $ trace "DDDDDDDDD" $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Sig (Var "_" 0) (Lam "_" Nothing (\_ -> Var "_" 0))) (Lam "_" Nothing (\_ -> (Var "?" 0))))) Nothing

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
      ta <- infer d span book ctx a
      tb <- infer d span book ctx b
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
      ta <- infer d span book ctx a
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
      eT <- infer d span book ctx e
      case force book eT of
        Eql t a b -> do
          let rewrittenCtx  = rewriteCtx d book a b ctx
          let rewrittenGoal = rewrite d book a b goal
          f' <- check d span book rewrittenCtx f rewrittenGoal
          e' <- check d span book ctx e eT
          return $ Rwt e' f'
        _ ->
          Fail $ trace "AAAAAAAA" $ TypeMismatch span (normalCtx book ctx) (normal book (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0))) (normal book eT) Nothing

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
      Fail $ trace "EEEEEEEEEEE" $ TypeMismatch span (normalCtx book ctx) (normal book goal) (Ref "Function" 1) Nothing

    -- ctx |- x : T
    -- ctx |- f : T -> T -> P
    -- ----------------------
    -- ctx |- (λ{&L:f} x) : P
    (App (SupM l f) x, _) -> do
      xT <- infer d span book ctx x
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
      do
      let fn_name = "$aux_"++show d
      x'    <- check d span book ctx x Bit
      goal' <- check d span book ctx goal Set
      res <- check d span book ctx (Let fn_name (Just (All Bit (Lam "_" Nothing (\_ -> goal')))) fn (\v -> App v x')) goal
      return res
    
    (App fn@(cut -> NatM z s) x, _) -> do
      let fn_name = "$aux_"++show d
      x'    <- check d span book ctx x Nat
      goal' <- check d span book ctx goal Set
      check d span book ctx (Let fn_name (Just (All Nat (Lam "_" Nothing (\_ -> goal')))) fn (\v -> App v x')) goal
    
    (App fn@(cut -> LstM n c) x@(cut -> Nil), _) -> do
      check d span book ctx n goal
    (App fn@(cut -> LstM n c) x, _) -> do
      let fn_name = "$aux_"++show d
      xT <- infer d span book ctx x
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
      xT' <- infer d span book ctx x
      xT  <- derefADT <$> check d span book ctx xT' Set

      case cut $ force book xT of
        Sig _ _ -> do
          x' <- check d span book ctx x xT
          goal' <- check d span book ctx goal Set
          check d span book ctx (Let fn_name (Just (All xT (Lam "_" Nothing (\_ -> goal')))) fn (\v -> App v x')) goal
        _       -> do
          Fail $ trace "FFFFFFFFFFF" $ TypeMismatch (getSpan span x) (normalCtx book ctx) (Var "Σ_:_._" 0) (normal book xT) Nothing
        where
          derefADT trm = case cut trm of
            Ref k i ->
              let xTbody = getDefn book k in
              case xTbody of
                Just (_, cut -> bod@(Sig (cut -> Enu _) _), _) -> bod
                _ -> trm
            _ -> trm

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
  t <- 
    -- trace ("-ver: " ++ show term ++ " :: " ++ show goal) $ 
    infer d span book ctx term
  if
    -- trace ("-verify: " ++ show term ++ " :: " ++ show t ++ " == " ++ show goal) $
    equal d book t goal
    then return term
    else Fail $ trace "GGGGGGG" $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book t) Nothing
