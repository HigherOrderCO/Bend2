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

-- Main eta-reduction function with lambda-inject optimization
reduceEtas :: Int -> Term -> Term
reduceEtas d t = case t of
  -- Check for the lambda-inject pattern: λx. ... (λ{...} x)
  Lam n ty f ->
    case isEtaLong n d (f (Var n d)) of
      Just (lmat, inj, hadTrust) ->
        let t'  = injectInto inj n lmat in
        let t'' = reduceEtas d t' in
        -- If a top-level `trust` was encountered on the path to the match,
        -- preserve it as an outer wrapper around the reduced case-tree.
        if hadTrust then Tst t'' else t''
      Nothing                    -> Lam n (fmap (reduceEtas d) ty) (\v -> reduceEtas (d+1) (f v))
  
  -- Recursive cases for all other constructors
  Var n i      -> Var n i
  Ref n i      -> Ref n i
  Sub t'       -> Sub (reduceEtas d t')
  Fix n f      -> Fix n (\v -> reduceEtas (d+1) (f v))
  Let k mt v f -> Let k (fmap (reduceEtas d) mt) (reduceEtas d v) (\v' -> reduceEtas (d+1) (f v'))
  Use k v f    -> Use k (reduceEtas d v) (\v' -> reduceEtas (d+1) (f v'))
  Set          -> Set
  Chk a b      -> Chk (reduceEtas d a) (reduceEtas d b)
  Tst a        -> Tst (reduceEtas d a)
  Emp          -> Emp
  EmpM         -> EmpM
  Uni          -> Uni
  One          -> One
  UniM a       -> UniM (reduceEtas d a)
  Bit          -> Bit
  Bt0          -> Bt0
  Bt1          -> Bt1
  BitM a b     -> BitM (reduceEtas d a) (reduceEtas d b)
  Nat          -> Nat
  Zer          -> Zer
  Suc n        -> Suc (reduceEtas d n)
  NatM a b     -> NatM (reduceEtas d a) (reduceEtas d b)
  Lst t'       -> Lst (reduceEtas d t')
  Nil          -> Nil
  Con h t'     -> Con (reduceEtas d h) (reduceEtas d t')
  LstM a b     -> LstM (reduceEtas d a) (reduceEtas d b)
  Enu ss       -> Enu ss
  Sym s        -> Sym s
  EnuM cs e    -> EnuM [(s, reduceEtas d v) | (s,v) <- cs] (reduceEtas d e)
  Num nt       -> Num nt
  Val nv       -> Val nv
  Op2 o a b    -> Op2 o (reduceEtas d a) (reduceEtas d b)
  Op1 o a      -> Op1 o (reduceEtas d a)
  Sig a b      -> Sig (reduceEtas d a) (reduceEtas d b)
  Tup a b      -> Tup (reduceEtas d a) (reduceEtas d b)
  SigM a       -> SigM (reduceEtas d a)
  All a b      -> All (reduceEtas d a) (reduceEtas d b)
  App f x      -> App (reduceEtas d f) (reduceEtas d x)
  Eql t' a b   -> Eql (reduceEtas d t') (reduceEtas d a) (reduceEtas d b)
  Rfl          -> Rfl
  EqlM f       -> EqlM (reduceEtas d f)
  Met n t' cs  -> Met n (reduceEtas d t') (map (reduceEtas d) cs)
  Era          -> Era
  Sup l a b    -> Sup (reduceEtas d l) (reduceEtas d a) (reduceEtas d b)
  SupM l f'    -> SupM (reduceEtas d l) (reduceEtas d f')
  Loc s t'     -> Loc s (reduceEtas d t')
  Log s x      -> Log (reduceEtas d s) (reduceEtas d x)
  Pri p        -> Pri p
  Pat ss ms cs -> Pat (map (reduceEtas d) ss) [(k, reduceEtas d v) | (k,v) <- ms] [(map (reduceEtas d) ps, reduceEtas d rhs) | (ps,rhs) <- cs]
  Frk l a b    -> Frk (reduceEtas d l) (reduceEtas d a) (reduceEtas d b)
  Rwt e f      -> Rwt (reduceEtas d e) (reduceEtas d f)

-- Check if a term matches the eta-long pattern: ... (λ{...} x)
-- Returns the lambda-match, an injection function, and whether a `trust`
-- marker was seen along the way (to be preserved outside after reduction).
isEtaLong :: Name -> Int -> Term -> Maybe (Term, Term -> Term, Bool)
isEtaLong target depth = go id depth False where
  go :: (Term -> Term) -> Int -> Bool -> Term -> Maybe (Term, Term -> Term, Bool)
  go inj d hadT term = case cut term of
    -- Found intermediate lambda - add to injection
    Lam n ty f -> 
      go (\h -> inj (Lam n ty (\_ -> h))) (d+1) hadT (f (Var n d))
    
    -- Found Let - add to injection
    Let k mt v f ->
      go (\h -> inj (Let k mt v (\_ -> h))) (d+1) hadT (f (Var k d))
    
    -- Found Use - add to injection
    Use k v f ->
      go (\h -> inj (Use k v (\_ -> h))) (d+1) hadT (f (Var k d))
    
    -- Found Chk - add to injection
    Chk x t ->
      go (\h -> inj (Chk h t)) d hadT x
    -- Found Tst - record and continue, but don't push it inside branches
    Tst x ->
      go inj d True x
    
    -- Found Loc: keep the location on the lambda-match itself instead of
    -- pushing it into the body. This ensures that errors during the check of
    -- the resulting λ-match are attributed to the original source span.
    Loc s x ->
      case go inj d hadT x of
        Just (lmat, injB, hadT') -> Just (Loc s lmat, injB, hadT')
        Nothing                   -> Nothing
    
    -- Found Log - add to injection
    Log s x ->
      go (\h -> inj (Log s h)) d hadT x

    -- Pass through single-body lambda-matches (commuting conversion)
    UniM b ->
      case go id d hadT b of
        Just (lmat, injB, tB) -> Just (lmat, \h -> inj (UniM (injB h)), tB)
        Nothing           -> Nothing

    SigM b ->
      case go id d hadT b of
        Just (lmat, injB, tB) -> Just (lmat, \h -> inj (SigM (injB h)), tB)
        Nothing           -> Nothing

    SupM l b ->
      case go id d hadT b of
        Just (lmat, injB, tB) -> Just (lmat, \h -> inj (SupM l (injB h)), tB)
        Nothing           -> Nothing

    EqlM b ->
      case go id d hadT b of
        Just (lmat, injB, tB) -> Just (lmat, \h -> inj (EqlM (injB h)), tB)
        Nothing           -> Nothing

    -- Conservative multi-arm pass-through: only if all arms agree on a common λ-match shape
    BitM t f ->
      case (go id d hadT t, go id d hadT f) of
        (Just (l1, injT, tT), Just (l2, injF, tF))
          | sameLambdaShape l1 l2 ->
              Just (l1, \h -> inj (BitM (injT h) (injF h)), tT || tF)
        _ -> Nothing

    NatM z s ->
      case (go id d hadT z, go id d hadT s) of
        (Just (l1, injZ, tZ), Just (l2, injS, tS))
          | sameLambdaShape l1 l2 ->
              Just (l1, \h -> inj (NatM (injZ h) (injS h)), tZ || tS)
        _ -> Nothing

    LstM n c ->
      case (go id d hadT n, go id d hadT c) of
        (Just (l1, injN, tN), Just (l2, injC, tC))
          | sameLambdaShape l1 l2 ->
              Just (l1, \h -> inj (LstM (injN h) (injC h)), tN || tC)
        _ -> Nothing

    EnuM cs e ->
      let rs = [(s, go id d hadT v) | (s,v) <- cs]
          re = go id d hadT e
      in
      if all (isJust . snd) rs && isJust re then
        let rcs       = [(s, fromJust m) | (s,m) <- rs]
            (l0, _, _) = fromJust re
            shapes = [lmShape l | (_, (l,_,_)) <- rcs] ++ [lmShape l0]
        in case sequence shapes of
             Just (sh0:rest) | all (== sh0) rest ->
               let injCs          = [(s, injB) | (s, (_, injB, _)) <- rcs]
                   (lmatE, injE, tE) = fromJust re
                   tAny          = tE || or [t | (_, (_,_,t)) <- rcs]
               in Just (lmatE, \h -> inj (EnuM [(s, injB h) | (s, injB) <- injCs] (injE h)), tAny)
             _ -> Nothing
      else Nothing

    -- Found application - check if it's (λ{...} x) or if we can pass through
    App f arg ->
      case (f, cut arg) of
        -- Check if f is a lambda-match (possibly wrapped in Loc) and arg is our target variable
        (lmat, Var v_n _) | v_n == target && isLambdaMatch lmat ->
          Just (lmat, inj, hadT)
        -- Otherwise, pass through the application
        _ -> go (\h -> inj (app h arg)) d hadT f
    
    -- Any other form doesn't match our pattern
    _ -> Nothing

-- FIXME: are the TODO cases below reachable? reason about it

-- Inject the injection function into each case of a lambda-match
injectInto :: (Term -> Term) -> Name -> Term -> Term
injectInto inj scrutName term = case term of
  -- Preserve location on the lambda-match node while injecting inside
  Loc sp t -> Loc sp (injectInto inj scrutName t)
  -- Empty match - no cases to inject into
  EmpM -> EmpM
  
  -- Unit match - inject into the single case
  UniM f -> UniM (injectBody [] inj scrutName (\_ -> One) f)
  
  -- Bool match - inject into both cases
  BitM f t -> BitM (injectBody [] inj scrutName (\_ -> Bt0) f) 
                   (injectBody [] inj scrutName (\_ -> Bt1) t)
  
  -- Nat match - special handling for successor case (1 field)
  NatM z s -> NatM (injectBody [] inj scrutName (\_ -> Zer) z) 
                   (injectBody ["p"] inj scrutName (\vars -> case vars of [p] -> Suc p; _ -> error $ "TODO: " ++ (show term)) s)
  
  -- List match - special handling for cons case (2 fields)
  LstM n c -> LstM (injectBody [] inj scrutName (\_ -> Nil) n) 
                   (injectBody ["h", "t"] inj scrutName (\vars -> case vars of [h,t] -> Con h t; _ -> error $ "TODO: " ++ (show term)) c)

  -- Enum match - inject into each case and default (apply default-case fix)
  EnuM cs e -> EnuM [(s, injectBody [] inj scrutName (\_ -> Sym s) v) | (s,v) <- cs]
                    (injectBody ["x"] inj scrutName (\vars -> case vars of [x] -> x; _ -> error $ "TODO: " ++ (show term)) e)
  
  -- Sigma match - special handling for pair case (2 fields)
  SigM f -> SigM (injectBody ["a", "b"] inj scrutName (\vars -> case vars of [a,b] -> Tup a b; _ -> error $ "TODO: " ++ (show term)) f)
  
  -- Superposition match - special handling (2 fields)
  SupM l f -> SupM l (injectBody ["a", "b"] inj scrutName (\vars -> case vars of [a,b] -> Sup l a b; _ -> error $ "TODO: " ++ (show term)) f)
  
  -- Equality match - inject into the single case
  EqlM f -> EqlM (injectBody [] inj scrutName (\_ -> Rfl) f)
  
  -- Not a lambda-match
  _ -> term

-- Helper to inject the injection function, skipping existing field lambdas
-- Also handles scrutinee reconstruction
injectBody :: [Name] -> (Term -> Term) -> Name -> ([Term] -> Term) -> Term -> Term
injectBody fields inj scrutName mkScrut body = go 0 fields [] [] body where
  go :: Int -> [Name] -> [Term] -> [Name] -> Term -> Term
  go d []     vars fieldNames body = 
    let scrutVal = mkScrut (reverse vars)
        -- Remove shadowed bindings from the injection
        cleanedInj = removeShadowed fieldNames inj
        -- Add scrutinee reconstruction if not shadowed
        fullInj = if scrutName `notElem` fieldNames
                  then \h -> Use scrutName scrutVal (\_ -> cleanedInj h)
                  else cleanedInj
    in fullInj body
  go d (f:fs) vars fieldNames body = case cut body of
    -- Existing field lambda - preserve it
    Lam n ty b -> Lam n ty (\v -> go (d+1) fs (v:vars) (n:fieldNames) (b v))
    -- Missing field lambda - add it
    _          -> Lam f Nothing (\v -> go (d+1) fs (v:vars) (f:fieldNames) body)

-- Remove shadowed bindings from an injection function
removeShadowed :: [Name] -> (Term -> Term) -> (Term -> Term)
removeShadowed fieldNames inj = \body -> removeFromTerm fieldNames (inj body) where
  removeFromTerm :: [Name] -> Term -> Term
  removeFromTerm names term = case term of
    -- Skip Use bindings that are shadowed
    Use k v f | k `elem` names -> removeFromTerm names (f (Var k 0))
    Use k v f                  -> Use k v (\x -> removeFromTerm names (f x))
    
    -- Skip Let bindings that are shadowed
    Let k mt v f | k `elem` names -> removeFromTerm names (f (Var k 0))
    Let k mt v f                  -> Let k mt v (\x -> removeFromTerm names (f x))
    
    -- For other constructs, just return as-is
    _ -> term

-- Check if a term is a lambda-match (one of the match constructors)
isLambdaMatch :: Term -> Bool
isLambdaMatch term = case term of
  EmpM     -> True
  UniM _   -> True
  BitM _ _ -> True
  NatM _ _ -> True
  LstM _ _ -> True
  EnuM _ _ -> True
  SigM _   -> True
  SupM _ _ -> True
  EqlM _   -> True
  Loc _ t  -> isLambdaMatch t
  _        -> False

-- Shapes of lambda-matches, used to conservatively commute multi-arm frames
data LmShape
  = LM_Emp
  | LM_Uni
  | LM_Bit
  | LM_Nat
  | LM_Lst
  | LM_Enu [String]
  | LM_Sig
  | LM_Sup
  | LM_Eql
  deriving (Eq, Show)

lmShape :: Term -> Maybe LmShape
lmShape t = case cut t of
  EmpM       -> Just LM_Emp
  UniM _     -> Just LM_Uni
  BitM _ _   -> Just LM_Bit
  NatM _ _   -> Just LM_Nat
  LstM _ _   -> Just LM_Lst
  EnuM cs _  -> Just (LM_Enu (map fst cs))
  SigM _     -> Just LM_Sig
  SupM _ _   -> Just LM_Sup
  EqlM _     -> Just LM_Eql
  Chk x _    -> lmShape x
  Loc _ x    -> lmShape x
  _          -> Nothing

sameLambdaShape :: Term -> Term -> Bool
sameLambdaShape a b = lmShape a == lmShape b

app :: Term -> Term -> Term
app (Lam k _ f) x = Use k x f
app f           x = App f x
