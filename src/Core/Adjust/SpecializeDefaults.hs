{-# LANGUAGE ViewPatterns #-}

-- Default Case Specialization
-- ============================
-- 
-- This module specializes default cases after pattern desugaring.
-- It replaces variable default cases with explicit constructor cases.

module Core.Adjust.SpecializeDefaults where

import Core.Type
import qualified Data.Map as M
import qualified Data.Set as S
import Core.Show

import Debug.Trace

-- | Main entry point for specializing defaults after desugaring
specializeDefaults :: Int -> Book -> Term -> Term
specializeDefaults d book (UniM f)       = UniM (specializeDefaults d book f)
specializeDefaults d book (Var n i)      = Var n i
specializeDefaults d book (Ref n i)      = Ref n i
specializeDefaults d book (Sub t)        = Sub (specializeDefaults d book t)
specializeDefaults d book (Fix n f)      = Fix n (\x -> specializeDefaults (d+1) book (f x))
specializeDefaults d book (Let k t v f)  = Let k (fmap (specializeDefaults d book) t) (specializeDefaults d book v) (\x -> specializeDefaults (d+1) book (f x))
specializeDefaults d book (Use k v f)    = Use k (specializeDefaults d book v) (\x -> specializeDefaults (d+1) book (f x))
specializeDefaults d book Set            = Set
specializeDefaults d book (Chk x t)      = Chk (specializeDefaults d book x) (specializeDefaults d book t)
specializeDefaults d book (Tst x)        = Tst (specializeDefaults d book x)
specializeDefaults d book Emp            = Emp
specializeDefaults d book EmpM           = EmpM
specializeDefaults d book Uni            = Uni
specializeDefaults d book One            = One
specializeDefaults d book Bit            = Bit
specializeDefaults d book Bt0            = Bt0
specializeDefaults d book Bt1            = Bt1
specializeDefaults d book (BitM f t)     = BitM (specializeDefaults d book f) (specializeDefaults d book t)
specializeDefaults d book Nat            = Nat
specializeDefaults d book Zer            = Zer
specializeDefaults d book (Suc n)        = Suc (specializeDefaults d book n)
specializeDefaults d book (NatM z s)     = NatM (specializeDefaults d book z) (specializeDefaults d book s)
specializeDefaults d book (Lst t)        = Lst (specializeDefaults d book t)
specializeDefaults d book Nil            = Nil
specializeDefaults d book (Con h t)      = Con (specializeDefaults d book h) (specializeDefaults d book t)
specializeDefaults d book (LstM n c)     = LstM (specializeDefaults d book n) (specializeDefaults d book c)
specializeDefaults d book (Enu s)        = Enu s
specializeDefaults d book (Sym s)        = Sym s
specializeDefaults d book (EnuM c e)     = EnuM [(s, specializeDefaults d book t) | (s, t) <- c] (fmap (specializeDefaults d book) e)
specializeDefaults d book (Sig a b)      = Sig (specializeDefaults d book a) (specializeDefaults d book b)
specializeDefaults d book (Tup a b)      = Tup (specializeDefaults d book a) (specializeDefaults d book b)
specializeDefaults d book (SigM (Lam n1 t1 f1)) = 
  trace ("FOUND SigM with Lam: " ++ n1) $
  case f1 (Var n1 0) of
    (Lam n2 t2 f2) -> 
      trace ("Second lambda found: " ++ n2) $
      case f2 (Var n2 0) of
        (App enumTerm scrutinee) -> 
          case cut enumTerm of
            (EnuM cases def) -> 
              trace ("FOUND PATTERN: SigM with two lambdas followed by App of EnuM - cases: " ++ show (map fst cases) ++ ", scrutinee: " ++ show scrutinee ++ ", second lambda var: " ++ n2) $
              SigM (Lam n1 t1 (\x1 -> Lam n2 t2 (\x2 -> App (specializeEnuM d book cases def n2) scrutinee)))
            _ -> 
              SigM (Lam n1 t1 (\x -> specializeDefaults (d+1) book (f1 x)))
        other -> 
          SigM (Lam n1 t1 (\x -> specializeDefaults (d+1) book (f1 x)))
    other -> 
      SigM (Lam n1 t1 (\x -> specializeDefaults (d+1) book (f1 x)))
specializeDefaults d book (SigM f)       = 
  trace ("FOUND SigM without Lam: " ++ show f) $
  SigM (specializeDefaults d book f)
specializeDefaults d book (All a b)      = All (specializeDefaults d book a) (specializeDefaults d book b)
specializeDefaults d book (Lam n t f)    = Lam n (fmap (specializeDefaults d book) t) (\x -> specializeDefaults (d+1) book (f x))
specializeDefaults d book (App f x)      = App (specializeDefaults d book f) (specializeDefaults d book x)
specializeDefaults d book (Eql t a b)    = Eql (specializeDefaults d book t) (specializeDefaults d book a) (specializeDefaults d book b)
specializeDefaults d book Rfl            = Rfl
specializeDefaults d book (EqlM f)       = EqlM (specializeDefaults d book f)
specializeDefaults d book (Met i t x)    = Met i (specializeDefaults d book t) (map (specializeDefaults d book) x)
specializeDefaults d book Era            = Era
specializeDefaults d book (Sup l a b)    = Sup (specializeDefaults d book l) (specializeDefaults d book a) (specializeDefaults d book b)
specializeDefaults d book (SupM l f)     = SupM (specializeDefaults d book l) (specializeDefaults d book f)
specializeDefaults d book (Frk l a b)    = Frk (specializeDefaults d book l) (specializeDefaults d book a) (specializeDefaults d book b)
specializeDefaults d book (Rwt e f)      = Rwt (specializeDefaults d book e) (specializeDefaults d book f)
specializeDefaults d book (Num t)        = Num t
specializeDefaults d book (Val v)        = Val v
specializeDefaults d book (Op2 o a b)    = Op2 o (specializeDefaults d book a) (specializeDefaults d book b)
specializeDefaults d book (Op1 o a)      = Op1 o (specializeDefaults d book a)
specializeDefaults d book (Pri p)        = Pri p
specializeDefaults d book (Log s x)      = Log (specializeDefaults d book s) (specializeDefaults d book x)
specializeDefaults d book (Loc s t)      = Loc s (specializeDefaults d book t)
specializeDefaults d book (Pat ss ms cs) = Pat (map (specializeDefaults d book) ss) ms [(map (specializeDefaults d book) ps, specializeDefaults d book b) | (ps, b) <- cs]


-- | Find which type a set of constructors belongs to
findTypeForConstructors :: Book -> [String] -> Maybe (Name, [(String, Int)])
findTypeForConstructors (Book _ _ typeCtors) ctors =
  case filter matchesType (M.toList typeCtors) of
    ((typeName, ctorList):_) -> Just (typeName, ctorList)
    [] -> Nothing
  where
    matchesType (_, typeCtrList) = 
      any (`elem` map fst typeCtrList) ctors

-- | Specialize a single constructor by adding it to the match with the default body
specializeConstructor :: String -> Int -> Term -> String -> Term
-- specializeConstructor ctorName arity (Lam k _ defaultBody) =
  -- trace ("SPECIALIZE CTOR: " ++ ctorName ++ " with arity " ++ show arity ++ ", default body: " ++ show (defaultBody (Var k 0))) $
  -- (defaultBody (Var k 0))

-- The structure of a constructor is sigma pairs ending with unit where the things are the fields and the rest is the rest of body.
-- Therefore what we need to add is continuous App matches on the correct structure ending with an `use` after the unit match when arity = 0
-- spec: λa:A. (λ{(,):λ_x1. λ_x2. (λ{&B:(λ{():0n})(_x2);&C:1n})(_x1)})(a)
specializeConstructor ctorName arity (Lam k _ defaultBody) scrutineeName = 
  trace ("SPECIALIZE CTOR: " ++ ctorName ++ " with arity " ++ show arity ++ ", default var: " ++ k ++ ", scrutinee: " ++ scrutineeName) $
  -- let body = (defaultBody (Var k 0))
  let body = (defaultBody (Var k 0))
  in trace ("Body for " ++ ctorName ++ ": " ++ show body) $
     buildSigmaChainWithReconstruction arity body scrutineeName ctorName k
specializeConstructor ctorName arity bod scrutineeName = bod

-- | Build sigma chain with reconstruction for constructor binding
buildSigmaChainWithReconstruction :: Int -> Term -> String -> String -> String -> Term
buildSigmaChainWithReconstruction arity body scrutineeName ctorName defaultVar = 
  buildSigmaChainWithFields arity body scrutineeName ctorName defaultVar []

-- | Helper that collects field variables
buildSigmaChainWithFields :: Int -> Term -> String -> String -> String -> [String] -> Term
buildSigmaChainWithFields 0 body scrutineeName ctorName defaultVar fieldVars = 
  -- let reconstructedValue = reconstructConstructor ctorName fieldVars
      -- bodyWithUse = Use defaultVar reconstructedValue (\_ -> body)
  -- in App (UniM bodyWithUse) (Var scrutineeName 0)
  --LOOK: CHANGED HERE
  let bodyWithUse = Use defaultVar (Sym ctorName) (\_ -> body)
  in App (UniM bodyWithUse) (Var scrutineeName 0)
buildSigmaChainWithFields arity body originalScrutinee ctorName defaultVar fieldVars = 
  let fieldVar = "$field" ++ show arity
      contVar = "$cont" ++ show arity
      newFieldVars = fieldVar : fieldVars
      innerChain = buildSigmaChainWithFields (arity - 1) body contVar ctorName defaultVar newFieldVars
  in App (SigM (Lam fieldVar Nothing (\_ -> Lam contVar Nothing (\_ -> innerChain)))) (Var originalScrutinee 0)

-- | Reconstruct constructor value as (@Ctor, (field1, (field2, ())))
reconstructConstructor :: String -> [String] -> Term
reconstructConstructor ctorName fields = 
  let ctorSym = Sym ctorName
      fieldsChain = foldr (\field acc -> Tup (Var field 0) acc) One (reverse fields)
  in Tup ctorSym fieldsChain

-- | Build sigma chain for constructor with given arity (old version, keeping for reference)
buildSigmaChain :: Int -> Term -> String -> Term
buildSigmaChain 0 body scrutineeName = 
  App (UniM body) (Var scrutineeName 0)
buildSigmaChain arity body originalScrutinee = 
  let fieldVar = "$field" ++ show arity
      contVar = "$cont" ++ show arity
      innerChain = buildSigmaChain (arity - 1) body contVar
  in App (SigM (Lam fieldVar Nothing (\_ -> Lam contVar Nothing (\_ -> innerChain)))) (Var originalScrutinee 0)

-- | Specializes an EnuM term by replacing default cases with explicit constructor cases
specializeEnuM :: Int -> Book -> [(String, Term)] -> Maybe Term -> String -> Term
specializeEnuM d book c Nothing scrutineeName = 
  EnuM [(s, specializeDefaults d book t) | (s, t) <- c] Nothing
specializeEnuM d book c (Just e) scrutineeName = 
  trace ("SPECIALIZING at depth " ++ show d ++ " - cases: " ++ show presentCases ++ ", has default" ++
         ", scrutinee: " ++ scrutineeName ++
         case typeInfo of
           Just (typeName, _) -> ", type: " ++ typeName ++ ", missing: " ++ show (map fst missingCtors)
           Nothing -> ", type: unknown") $
    EnuM (existingCases ++ newCases) Nothing
  where
    presentCases = map fst c
    typeInfo = findTypeForConstructors book presentCases
    missingCtors = case typeInfo of
      Just (typeName, allCtors) -> filter (\(name, _) -> name `notElem` presentCases) allCtors
      Nothing -> []
    existingCases = [(s, specializeDefaults d book t) | (s, t) <- c]
    newCases = [(name, specializeConstructor name arity e scrutineeName) | (name, arity) <- missingCtors]
