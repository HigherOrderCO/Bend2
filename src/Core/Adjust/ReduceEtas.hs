{-./../Type.hs-}

module Core.Adjust.ReduceEtas where

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

import Core.Type
import qualified Data.Set as S
import Debug.Trace

-- Eta-reducer entry point
reduceEtas :: Int -> Term -> Term
reduceEtas d t = go d t where
  -- Check for the lambda-inject pattern: λx. ... (λ{...} x)
  go d (Lam n ty f) =
    case isEtaLong n d (f (Var n d)) of
      Just (lmt,inj) -> reduceEtas d (injectInto inj n lmt)
      Nothing        -> Lam n (fmap (go d) ty) (\v -> go (d+1) (f v))
  go d (Var n i)      = Var n i
  go d (Sub t')       = Sub (go d t')
  go d (Fix n f)      = Fix n (\v -> go (d+1) (f v))
  go d (Let k mt v f) = Let k (fmap (go d) mt) (go d v) (\v' -> go (d+1) (f v'))
  go d (Use k v f)    = Use k (go d v) (\v' -> go (d+1) (f v'))
  go d Set            = Set
  go d (Chk a b)      = Chk (go d a) (go d b)
  go d Emp            = Emp
  go d EmpM           = EmpM
  go d Uni            = Uni
  go d One            = One
  go d (UniM a)       = UniM (go d a)
  go d Bit            = Bit
  go d Bt0            = Bt0
  go d Bt1            = Bt1
  go d (BitM a b)     = BitM (go d a) (go d b)
  go d Nat            = Nat
  go d Zer            = Zer
  go d (Suc n)        = Suc (go d n)
  go d (NatM a b)     = NatM (go d a) (go d b)
  go d (Lst t')       = Lst (go d t')
  go d Nil            = Nil
  go d (Con h t')     = Con (go d h) (go d t')
  go d (LstM a b)     = LstM (go d a) (go d b)
  go d (ADT n ps)     = ADT n (map (go d) ps)
  go d (Ctr n as)     = Ctr n (map (go d) as)
  go d (ADTM n cs df) = ADTM n [(c, go d v) | (c,v) <- cs] (fmap (go d) df)
  go d (Num nt)       = Num nt
  go d (Val nv)       = Val nv
  go d (Op2 o a b)    = Op2 o (go d a) (go d b)
  go d (Op1 o a)      = Op1 o (go d a)
  go d (Sig a b)      = Sig (go d a) (go d b)
  go d (Tup a b)      = Tup (go d a) (go d b)
  go d (SigM a)       = SigM (go d a)
  go d (All a b)      = All (go d a) (go d b)
  go d (App f x)      = App (go d f) (go d x)
  go d (Eql t' a b)   = Eql (go d t') (go d a) (go d b)
  go d Rfl            = Rfl
  go d (EqlM f)       = EqlM (go d f)
  go d (Met n t' cs)  = Met n (go d t') (map (go d) cs)
  go d Era            = Era
  go d (Sup l a b)    = Sup (go d l) (go d a) (go d b)
  go d (SupM l f')    = SupM (go d l) (go d f')
  go d (Loc s t')     = Loc s (go d t')
  go d (Log s x)      = Log (go d s) (go d x)
  go d (Pri p)        = Pri p
  go d (Pat ss ms cs) = Pat (map (go d) ss) [(k, go d v) | (k,v) <- ms] [(map (go d) ps, go d rhs) | (ps,rhs) <- cs]
  go d (Frk l a b)    = Frk (go d l) (go d a) (go d b)
  go d (Rwt e f)      = Rwt (go d e) (go d f)
  go d (Ref n i)      = Ref n i

-- Check if a term matches the eta-long pattern: ... (λ{...} x)
-- Returns the lambda-match and an injection function
isEtaLong :: Name -> Int -> Term -> Maybe (Term, Term -> Term)
isEtaLong target depth = go id depth where
  go :: (Term -> Term) -> Int -> Term -> Maybe (Term, Term -> Term)
  go inj d term = case cut term of
    -- Found intermediate lambda - add to injection
    Lam n ty f -> 
      go (\h -> inj (Lam n ty (\_ -> h))) (d+1) (f (Var n d))
    
    -- Found Let - add to injection
    Let k mt v f ->
      go (\h -> inj (Let k mt v (\_ -> h))) (d+1) (f (Var k d))
    
    -- Found Use - add to injection
    Use k v f ->
      go (\h -> inj (Use k v (\_ -> h))) (d+1) (f (Var k d))
    
    -- Found Chk - add to injection
    Chk x t ->
      go (\h -> inj (Chk h t)) d x
    
    -- Found Loc - add to injection
    Loc s x ->
      go (\h -> inj (Loc s h)) d x
    
    -- Found Log - add to injection
    Log s x ->
      go (\h -> inj (Log s h)) d x
    
    -- Found application - check if it's (λ{...} x) or if we can pass through
    App f arg ->
      case (cut f, cut arg) of
        -- Check if f is a lambda-match and arg is our target variable
        (lmat, Var v_n _) | v_n == target && isLambdaMatch lmat ->
          Just (lmat, inj)
        -- Otherwise, pass through the application
        _ -> go (\h -> inj (app h arg)) d f
    
    -- Any other form doesn't match our pattern
    _ -> Nothing

-- Inject the injection function into each case of a lambda-match
injectInto :: (Term -> Term) -> Name -> Term -> Term
injectInto inj scrutName term = case term of
  -- Empty match - no cases to inject into
  EmpM -> EmpM
  
  -- Unit match - inject into the single case
  UniM f -> UniM (injectBody [] inj scrutName (\_ -> One) f)
  
  -- Bool match - inject into both cases
  BitM f t -> BitM (injectBody [] inj scrutName (\_ -> Bt0) f) 
                   (injectBody [] inj scrutName (\_ -> Bt1) t)
  
  -- Nat match - special handling for successor case (1 field)
  NatM z s -> NatM (injectBody [] inj scrutName (\_ -> Zer) z) 
                   (injectBody ["p"] inj scrutName (\vars -> case vars of [p] -> Suc p; _ -> Era) s)
  
  -- List match - special handling for cons case (2 fields)
  LstM n c -> LstM (injectBody [] inj scrutName (\_ -> Nil) n) 
                   (injectBody ["h", "t"] inj scrutName (\vars -> case vars of [h,t] -> Con h t; _ -> Era) c)
  
  -- ADT match - inject into each case and default
  ADTM adtName cs df -> ADTM adtName [(cname, injectBody [] inj scrutName (\_ -> Ctr cname []) v) | (cname,v) <- cs] 
                                      (fmap (injectBody ["_"] inj scrutName (\_ -> Era)) df)
  
  -- Sigma match - special handling for pair case (2 fields)
  SigM f -> SigM (injectBody ["a", "b"] inj scrutName (\vars -> case vars of [a,b] -> Tup a b; _ -> Era) f)
  
  -- Superposition match - special handling (2 fields)
  SupM l f -> SupM l (injectBody ["a", "b"] inj scrutName (\vars -> case vars of [a,b] -> Sup l a b; _ -> Era) f)
  
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
  EmpM       -> True
  UniM _     -> True
  BitM _ _   -> True
  NatM _ _   -> True
  LstM _ _   -> True
  ADTM _ _ _ -> True
  SigM _     -> True
  SupM _ _   -> True
  EqlM _     -> True
  _          -> False

app :: Term -> Term -> Term
app (Lam k _ f) x = Use k x f
app f           x = App f x
