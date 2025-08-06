{-./../Type.hs-}

-- module Core.Adjust.ReduceEtas where

-- -- Eta-Form
-- -- ========
-- --
-- -- This module performs eta-reduction with lambda-inject optimization, transforming
-- -- nested lambda-match patterns into more efficient forms.
-- --
-- -- Basic Transformation:
-- -- --------------------
-- -- λx. λy. λz. (λ{...} x) ~> λ{0n:λy.λz.A; 1n+:λy.λz.B}
-- --
-- -- The optimization moves intermediate lambdas inside match branches. It also handles
-- -- passthrough constructs (Let, Use, Chk, Loc, Log, App) and reconstructs the scrutinee
-- -- when needed using 'use' bindings.
-- --
-- -- Examples:
-- -- ---------
-- -- 1. Simple eta-reduction:
-- --    λn. (λ{0n:Z; 1n+:S} n) ~> λ{0n:Z; 1n+:S}
-- --
-- -- 2. With intermediate lambdas:
-- --    λa. λb. (λ{0n:Z; 1n+:S} a) ~> λ{0n:λb.Z; 1n+:λp.λb.S}
-- --
-- -- 3. With scrutinee reconstruction:
-- --    λa. (λ{0n:a; 1n+:λp. 1n+p} a) ~> λ{0n:use a=0n a; 1n+:λp. use a=1n+p 1n+p}
-- --
-- -- 4. Reconstruction disabled when field name matches scrutinee:
-- --    λb. (λ{0n:Z; 1n+:λb. S} b) ~> λ{0n:use b=0n Z; 1n+:λb. S} (no reconstruction in 1n+ case)
-- --
-- -- Key Points:
-- -- ----------
-- -- - Field lambdas are injected first, then intermediate constructs
-- -- - Scrutinee is reconstructed with 'use' bindings unless field names conflict
-- -- - Handles Let, Use, Chk, Loc, Log, and App as passthrough constructs

-- import Core.Type
-- import qualified Data.Set as S
-- import Debug.Trace

-- -- Main eta-reduction function with lambda-inject optimization
-- reduceEtas :: Int -> Term -> Term
-- reduceEtas d t = case t of
  -- -- Check for the lambda-inject pattern: λx. ... (λ{...} x)
  -- Lam n ty f ->
    -- case isEtaLong n d (f (Var n d)) of
      -- Just (lmat, inj) ->
        -- let t'  = injectInto inj n lmat in
        -- let t'' = reduceEtas d t' in
        -- -- trace ("ETA:\n> " ++ show t ++ "\n> " ++ show t' ++ "\n> " ++ show t'') $
        -- t''
      -- Nothing          -> Lam n (fmap (reduceEtas d) ty) (\v -> reduceEtas (d+1) (f v))
  
  -- -- Recursive cases for all other constructors
  -- Var n i      -> Var n i
  -- Ref n i      -> Ref n i
  -- Sub t'       -> Sub (reduceEtas d t')
  -- Fix n f      -> Fix n (\v -> reduceEtas (d+1) (f v))
  -- Let k mt v f -> Let k (fmap (reduceEtas d) mt) (reduceEtas d v) (\v' -> reduceEtas (d+1) (f v'))
  -- Use k v f    -> Use k (reduceEtas d v) (\v' -> reduceEtas (d+1) (f v'))
  -- Set          -> Set
  -- Chk a b      -> Chk (reduceEtas d a) (reduceEtas d b)
  -- Emp          -> Emp
  -- EmpM         -> EmpM
  -- Uni          -> Uni
  -- One          -> One
  -- UniM a       -> UniM (reduceEtas d a)
  -- Bit          -> Bit
  -- Bt0          -> Bt0
  -- Bt1          -> Bt1
  -- BitM a b     -> BitM (reduceEtas d a) (reduceEtas d b)
  -- Nat          -> Nat
  -- Zer          -> Zer
  -- Suc n        -> Suc (reduceEtas d n)
  -- NatM a b     -> NatM (reduceEtas d a) (reduceEtas d b)
  -- Lst t'       -> Lst (reduceEtas d t')
  -- Nil          -> Nil
  -- Con h t'     -> Con (reduceEtas d h) (reduceEtas d t')
  -- LstM a b     -> LstM (reduceEtas d a) (reduceEtas d b)
  -- Enu ss       -> Enu ss
  -- Sym s        -> Sym s
  -- EnuM cs e    -> EnuM [(s, reduceEtas d v) | (s,v) <- cs] (reduceEtas d e)
  -- Num nt       -> Num nt
  -- Val nv       -> Val nv
  -- Op2 o a b    -> Op2 o (reduceEtas d a) (reduceEtas d b)
  -- Op1 o a      -> Op1 o (reduceEtas d a)
  -- Sig a b      -> Sig (reduceEtas d a) (reduceEtas d b)
  -- Tup a b      -> Tup (reduceEtas d a) (reduceEtas d b)
  -- SigM a       -> SigM (reduceEtas d a)
  -- All a b      -> All (reduceEtas d a) (reduceEtas d b)
  -- App f x      -> App (reduceEtas d f) (reduceEtas d x)
  -- Eql t' a b   -> Eql (reduceEtas d t') (reduceEtas d a) (reduceEtas d b)
  -- Rfl          -> Rfl
  -- EqlM f       -> EqlM (reduceEtas d f)
  -- Met n t' cs  -> Met n (reduceEtas d t') (map (reduceEtas d) cs)
  -- Era          -> Era
  -- Sup l a b    -> Sup (reduceEtas d l) (reduceEtas d a) (reduceEtas d b)
  -- SupM l f'    -> SupM (reduceEtas d l) (reduceEtas d f')
  -- Loc s t'     -> Loc s (reduceEtas d t')
  -- Log s x      -> Log (reduceEtas d s) (reduceEtas d x)
  -- Pri p        -> Pri p
  -- Pat ss ms cs -> Pat (map (reduceEtas d) ss) [(k, reduceEtas d v) | (k,v) <- ms] [(map (reduceEtas d) ps, reduceEtas d rhs) | (ps,rhs) <- cs]
  -- Frk l a b    -> Frk (reduceEtas d l) (reduceEtas d a) (reduceEtas d b)
  -- Rwt e f      -> Rwt (reduceEtas d e) (reduceEtas d f)

-- -- Check if a term matches the eta-long pattern: ... (λ{...} x)
-- -- Returns the lambda-match and an injection function
-- isEtaLong :: Name -> Int -> Term -> Maybe (Term, Term -> Term)
-- isEtaLong target depth = go id depth where
  -- go :: (Term -> Term) -> Int -> Term -> Maybe (Term, Term -> Term)
  -- go inj d term = case cut term of
    -- -- Found intermediate lambda - add to injection
    -- Lam n ty f -> 
      -- go (\h -> inj (Lam n ty (\_ -> h))) (d+1) (f (Var n d))
    
    -- -- Found Let - add to injection
    -- Let k mt v f ->
      -- go (\h -> inj (Let k mt v (\_ -> h))) (d+1) (f (Var k d))
    
    -- -- Found Use - add to injection
    -- Use k v f ->
      -- go (\h -> inj (Use k v (\_ -> h))) (d+1) (f (Var k d))
    
    -- -- Found Chk - add to injection
    -- Chk x t ->
      -- go (\h -> inj (Chk h t)) d x
    
    -- -- Found Loc - add to injection
    -- Loc s x ->
      -- go (\h -> inj (Loc s h)) d x
    
    -- -- Found Log - add to injection
    -- Log s x ->
      -- go (\h -> inj (Log s h)) d x
    
    -- -- Found application - check if it's (λ{...} x) or if we can pass through
    -- App f arg ->
      -- case (cut f, cut arg) of
        -- -- Check if f is a lambda-match and arg is our target variable
        -- (lmat, Var v_n _) | v_n == target && isLambdaMatch lmat ->
          -- Just (lmat, inj)
        -- -- Otherwise, pass through the application
        -- _ -> go (\h -> inj (app h arg)) d f
    
    -- -- Any other form doesn't match our pattern
    -- _ -> Nothing

-- -- Inject the injection function into each case of a lambda-match
-- injectInto :: (Term -> Term) -> Name -> Term -> Term
-- injectInto inj scrutName term = case term of
  -- -- Empty match - no cases to inject into
  -- EmpM -> EmpM
  
  -- -- Unit match - inject into the single case
  -- UniM f -> UniM (injectBody [] inj scrutName (\_ -> One) f)
  
  -- -- Bool match - inject into both cases
  -- BitM f t -> BitM (injectBody [] inj scrutName (\_ -> Bt0) f) 
                   -- (injectBody [] inj scrutName (\_ -> Bt1) t)
  
  -- -- Nat match - special handling for successor case (1 field)
  -- NatM z s -> NatM (injectBody [] inj scrutName (\_ -> Zer) z) 
                   -- (injectBody ["p"] inj scrutName (\vars -> case vars of [p] -> Suc p; _ -> Era) s)
  
  -- -- List match - special handling for cons case (2 fields)
  -- LstM n c -> LstM (injectBody [] inj scrutName (\_ -> Nil) n) 
                   -- (injectBody ["h", "t"] inj scrutName (\vars -> case vars of [h,t] -> Con h t; _ -> Era) c)
  
  -- -- Enum match - inject into each case and default
  -- EnuM cs e -> EnuM [(s, injectBody [] inj scrutName (\_ -> Sym s) v) | (s,v) <- cs] 
                    -- (injectBody [] inj scrutName (\_ -> Era) e)
  
  -- -- Sigma match - special handling for pair case (2 fields)
  -- SigM f -> SigM (injectBody ["a", "b"] inj scrutName (\vars -> case vars of [a,b] -> Tup a b; _ -> Era) f)
  
  -- -- Superposition match - special handling (2 fields)
  -- SupM l f -> SupM l (injectBody ["a", "b"] inj scrutName (\vars -> case vars of [a,b] -> Sup l a b; _ -> Era) f)
  
  -- -- Equality match - inject into the single case
  -- EqlM f -> EqlM (injectBody [] inj scrutName (\_ -> Rfl) f)
  
  -- -- Not a lambda-match
  -- _ -> term

-- -- Helper to inject the injection function, skipping existing field lambdas
-- -- Also handles scrutinee reconstruction
-- injectBody :: [Name] -> (Term -> Term) -> Name -> ([Term] -> Term) -> Term -> Term
-- injectBody fields inj scrutName mkScrut body = go 0 fields [] [] body where
  -- go :: Int -> [Name] -> [Term] -> [Name] -> Term -> Term
  -- go d []     vars fieldNames body = 
    -- let scrutVal = mkScrut (reverse vars)
        -- -- Remove shadowed bindings from the injection
        -- cleanedInj = removeShadowed fieldNames inj
        -- -- Add scrutinee reconstruction if not shadowed
        -- fullInj = if scrutName `notElem` fieldNames
                  -- then \h -> Use scrutName scrutVal (\_ -> cleanedInj h)
                  -- else cleanedInj
    -- in fullInj body
  -- go d (f:fs) vars fieldNames body = case cut body of
    -- -- Existing field lambda - preserve it
    -- Lam n ty b -> Lam n ty (\v -> go (d+1) fs (v:vars) (n:fieldNames) (b v))
    -- -- Missing field lambda - add it
    -- _          -> Lam f Nothing (\v -> go (d+1) fs (v:vars) (f:fieldNames) body)

-- -- Remove shadowed bindings from an injection function
-- removeShadowed :: [Name] -> (Term -> Term) -> (Term -> Term)
-- removeShadowed fieldNames inj = \body -> removeFromTerm fieldNames (inj body) where
  -- removeFromTerm :: [Name] -> Term -> Term
  -- removeFromTerm names term = case term of
    -- -- Skip Use bindings that are shadowed
    -- Use k v f | k `elem` names -> removeFromTerm names (f (Var k 0))
    -- Use k v f                  -> Use k v (\x -> removeFromTerm names (f x))
    
    -- -- Skip Let bindings that are shadowed
    -- Let k mt v f | k `elem` names -> removeFromTerm names (f (Var k 0))
    -- Let k mt v f                  -> Let k mt v (\x -> removeFromTerm names (f x))
    
    -- -- For other constructs, just return as-is
    -- _ -> term

-- -- Check if a term is a lambda-match (one of the match constructors)
-- isLambdaMatch :: Term -> Bool
-- isLambdaMatch term = case term of
  -- EmpM     -> True
  -- UniM _   -> True
  -- BitM _ _ -> True
  -- NatM _ _ -> True
  -- LstM _ _ -> True
  -- EnuM _ _ -> True
  -- SigM _   -> True
  -- SupM _ _ -> True
  -- EqlM _   -> True
  -- _        -> False

-- app :: Term -> Term -> Term
-- app (Lam k _ f) x = Use k x f
-- app f           x = App f x

-- TODO: update the Eta-Form module

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

-- Main eta-reduction function with lambda-inject optimization
reduceEtas :: Int -> Term -> Term
reduceEtas d t = case t of
  -- Check for the lambda-inject pattern: λx. ... (λ{...} x)
  Lam n ty f ->
    case isEtaLong n d (f (Var n d)) of
      Just (lmat, inj) ->
        let t'  = injectInto inj n lmat in
        let t'' = reduceEtas d t' in
        -- trace ("ETA:\n> " ++ show t ++ "\n> " ++ show t' ++ "\n> " ++ show t'') $
        t''
      Nothing          -> Lam n (fmap (reduceEtas d) ty) (\v -> reduceEtas (d+1) (f v))
  
  -- Recursive cases for all other constructors
  Var n i      -> Var n i
  Ref n i      -> Ref n i
  Sub t'       -> Sub (reduceEtas d t')
  Fix n f      -> Fix n (\v -> reduceEtas (d+1) (f v))
  Let k mt v f -> Let k (fmap (reduceEtas d) mt) (reduceEtas d v) (\v' -> reduceEtas (d+1) (f v'))
  Use k v f    -> Use k (reduceEtas d v) (\v' -> reduceEtas (d+1) (f v'))
  Set          -> Set
  Chk a b      -> Chk (reduceEtas d a) (reduceEtas d b)
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
  ADT n ps     -> ADT n (map (reduceEtas d) ps)
  Ctr n as     -> Ctr n (map (reduceEtas d) as)
  ADTM n cs df -> ADTM n [(c, reduceEtas d v) | (c,v) <- cs] (fmap (reduceEtas d) df)
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
                                      (fmap (injectBody [] inj scrutName (\_ -> Era)) df)
  
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

