-- Default case specialization for pattern matching
-- ==================================================
-- After pattern desugaring, this phase detects enum matches with default
-- cases and replaces them with explicit constructor cases. This enables
-- better optimization and ensures all constructors are handled explicitly.

{-# LANGUAGE ViewPatterns #-}

module Core.Adjust.SpecializeDefaults (specializeDefaults) where

import qualified Data.Map as M

import Core.Type

-- Public API
-- ----------

specializeDefaults :: Int -> Book -> Term -> Term
specializeDefaults d book term = case term of
  -- Variables
  Var n i -> Var n i
  Ref n i -> Ref n i
  Sub t   -> Sub (specializeDefaults d book t)
  
  -- Definitions
  Fix n f      -> Fix n (\x -> specializeDefaults (d+1) book (f x))
  Let k t v f  -> Let k (fmap (specializeDefaults d book) t) (specializeDefaults d book v) (\x -> specializeDefaults (d+1) book (f x))
  Use k v f    -> Use k (specializeDefaults d book v) (\x -> specializeDefaults (d+1) book (f x))
  
  -- Universe
  Set -> Set
  
  -- Annotation
  Chk x t -> Chk (specializeDefaults d book x) (specializeDefaults d book t)
  Tst x   -> Tst (specializeDefaults d book x)
  
  -- Empty
  Emp  -> Emp
  EmpM -> EmpM
  
  -- Unit
  Uni       -> Uni
  One       -> One
  UniM f    -> UniM (specializeDefaults d book f)
  
  -- Bool
  Bit       -> Bit
  Bt0       -> Bt0
  Bt1       -> Bt1
  BitM f t  -> BitM (specializeDefaults d book f) (specializeDefaults d book t)
  
  -- Nat
  Nat       -> Nat
  Zer       -> Zer
  Suc n     -> Suc (specializeDefaults d book n)
  NatM z s  -> NatM (specializeDefaults d book z) (specializeDefaults d book s)
  
  -- List
  Lst t     -> Lst (specializeDefaults d book t)
  Nil       -> Nil
  Con h t   -> Con (specializeDefaults d book h) (specializeDefaults d book t)
  LstM n c  -> LstM (specializeDefaults d book n) (specializeDefaults d book c)
  
  -- Enum
  Enu s     -> Enu s
  Sym s     -> Sym s
  EnuM c e  -> EnuM [(s, specializeDefaults d book t) | (s, t) <- c] (fmap (specializeDefaults d book) e)
  
  -- Pair
  Sig a b   -> Sig (specializeDefaults d book a) (specializeDefaults d book b)
  Tup a b   -> Tup (specializeDefaults d book a) (specializeDefaults d book b)
  
  -- Special case: SigM with pattern matching structure
  SigM lam -> case lam of
    Lam n1 t1 f1 ->
      case f1 (Var n1 0) of
        Lam n2 t2 f2 ->
          case f2 (Var n2 0) of
            App enumTerm scrutinee ->
              case cut enumTerm of
                EnuM cases def ->
                  SigM (Lam n1 t1 (\x1 -> Lam n2 t2 (\x2 -> App (specializeEnuM d book cases def n2) scrutinee)))
                _ -> SigM (Lam n1 t1 (\x -> specializeDefaults (d+1) book (f1 x)))
            _ -> SigM (Lam n1 t1 (\x -> specializeDefaults (d+1) book (f1 x)))
        _ -> SigM (Lam n1 t1 (\x -> specializeDefaults (d+1) book (f1 x)))
    _ -> SigM (specializeDefaults d book lam)
  
  -- Function
  All a b   -> All (specializeDefaults d book a) (specializeDefaults d book b)
  Lam n t f -> Lam n (fmap (specializeDefaults d book) t) (\x -> specializeDefaults (d+1) book (f x))
  App f x   -> App (specializeDefaults d book f) (specializeDefaults d book x)
  
  -- Equality
  Eql t a b -> Eql (specializeDefaults d book t) (specializeDefaults d book a) (specializeDefaults d book b)
  Rfl       -> Rfl
  EqlM f    -> EqlM (specializeDefaults d book f)
  Rwt e f   -> Rwt (specializeDefaults d book e) (specializeDefaults d book f)
  
  -- MetaVar
  Met i t x -> Met i (specializeDefaults d book t) (map (specializeDefaults d book) x)
  
  -- Superposition
  Era       -> Era
  Sup l a b -> Sup (specializeDefaults d book l) (specializeDefaults d book a) (specializeDefaults d book b)
  SupM l f  -> SupM (specializeDefaults d book l) (specializeDefaults d book f)
  
  -- Errors
  Loc s t   -> Loc s (specializeDefaults d book t)
  
  -- Logging
  Log s x   -> Log (specializeDefaults d book s) (specializeDefaults d book x)
  
  -- Primitive
  Pri p     -> Pri p
  
  -- Numbers
  Num t     -> Num t
  Val v     -> Val v
  Op2 o a b -> Op2 o (specializeDefaults d book a) (specializeDefaults d book b)
  Op1 o a   -> Op1 o (specializeDefaults d book a)
  
  -- Sugars (should not appear after desugaring)
  Pat _ _ _ -> error "Pattern should not appear after desugaring"
  Frk l a b -> Frk (specializeDefaults d book l) (specializeDefaults d book a) (specializeDefaults d book b)

-- Internal
-- --------

-- Find which type a set of constructors belongs to
findTypeForConstructors :: Book -> [String] -> Maybe (Name, [(String, Int)])
findTypeForConstructors (Book _ _ typeCtors) ctors =
  case filter matchesType (M.toList typeCtors) of
    ((typeName, ctorList):_) -> Just (typeName, ctorList)
    []                        -> Nothing
  where
    matchesType (_, typeCtrList) = any (`elem` map fst typeCtrList) ctors

-- Specialize a single constructor by adding it to the match with the default body
-- The structure of a constructor is sigma pairs ending with unit. Fields are
-- bound sequentially and the constructor symbol is bound with a use statement.
specializeConstructor :: String -> Int -> Term -> String -> Term
specializeConstructor ctorName arity (Lam k _ defaultBody) scrutineeName =
  let body = defaultBody (Var k 0) in
  buildSigmaChain arity body scrutineeName ctorName k
specializeConstructor _ _ term _ = term

-- Build sigma chain for constructor with given arity
buildSigmaChain :: Int -> Term -> String -> String -> String -> Term
buildSigmaChain arity body scrutineeName ctorName defaultVar =
  buildSigmaChainRec arity body scrutineeName ctorName defaultVar []

-- Recursive helper for building sigma chains
buildSigmaChainRec :: Int -> Term -> String -> String -> String -> [String] -> Term
buildSigmaChainRec 0 body scrutineeName ctorName defaultVar _ =
  -- Base case: bind constructor symbol and apply to unit match
  let bodyWithUse = Use defaultVar (Sym ctorName) (\_ -> body) in
  App (UniM bodyWithUse) (Var scrutineeName 0)
buildSigmaChainRec arity body originalScrutinee ctorName defaultVar fieldVars =
  -- Recursive case: build nested sigma matches for fields
  let fieldVar = "$field" ++ show arity
      contVar  = "$cont" ++ show arity
      newFieldVars = fieldVar : fieldVars
      innerChain = buildSigmaChainRec (arity - 1) body contVar ctorName defaultVar newFieldVars in
  App (SigM (Lam fieldVar Nothing (\_ -> Lam contVar Nothing (\_ -> innerChain)))) (Var originalScrutinee 0)

-- Specializes an EnuM term by replacing default cases with explicit constructor cases
specializeEnuM :: Int -> Book -> [(String, Term)] -> Maybe Term -> String -> Term
specializeEnuM d book cases Nothing scrutineeName =
  -- No default case: just recurse on existing cases
  EnuM [(s, specializeDefaults d book t) | (s, t) <- cases] Nothing
specializeEnuM d book cases (Just defaultTerm) scrutineeName =
  -- Has default case: expand to all missing constructors
  EnuM (existingCases ++ newCases) Nothing
  where
    presentCases  = map fst cases
    typeInfo      = findTypeForConstructors book presentCases
    missingCtors  = case typeInfo of
      Just (_, allCtors) -> filter (\(name, _) -> name `notElem` presentCases) allCtors
      Nothing            -> []
    existingCases = [(s, specializeDefaults d book t) | (s, t) <- cases]
    newCases      = [(name, specializeConstructor name arity defaultTerm scrutineeName) | (name, arity) <- missingCtors]
