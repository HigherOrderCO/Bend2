{-# LANGUAGE ViewPatterns #-}

-- Default Case Specialization
-- ============================
-- 
-- This module specializes pattern matches with default cases by expanding them
-- to cover all constructors of the type explicitly. This transformation happens
-- before flattening, making it cleaner to manage.
--
-- Example:
--   match a: case @E{n,f}: @E{n,f} ; case v: v
-- becomes:
--   match a: case @E{n,f}: @E{n,f} ; case @F{h}: use v = @F{h}; v
--
-- The default variable is bound to the reconstructed term using 'use'.

module Core.Adjust.SpecializeDefaults where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List (find, partition)
import Debug.Trace

import Core.Type
import Core.Show
import Core.Bind

-- | Main entry point: specialize all default cases in a term
specializeDefaults :: Int -> Book -> Term -> Term
specializeDefaults d book term = go d term where
  go d (Pat scruts moves cases) = 
    Pat scruts moves (specializePatCases d book scruts cases)
  go d (Loc s t) = Loc s (go d t)
  go d (Fix n f) = Fix n (\x -> go (d+1) (f x))
  go d (Let k t v f) = Let k (fmap (go d) t) (go d v) (\x -> go (d+1) (f x))
  go d (Use k v f) = Use k (go d v) (\x -> go (d+1) (f x))
  go d (Lam n t f) = Lam n (fmap (go d) t) (\x -> go (d+1) (f x))
  go d (App f x) = App (go d f) (go d x)
  go d (All a b) = All (go d a) (go d b)
  go d (Sig a b) = Sig (go d a) (go d b)
  go d (Tup a b) = Tup (go d a) (go d b)
  go d (Con h t) = Con (go d h) (go d t)
  go d (Suc n) = Suc (go d n)
  go d (Op2 o a b) = Op2 o (go d a) (go d b)
  go d (Op1 o a) = Op1 o (go d a)
  go d (Chk x t) = Chk (go d x) (go d t)
  go d (Tst x) = Tst (go d x)
  go d (UniM f) = UniM (go d f)
  go d (BitM f t) = BitM (go d f) (go d t)
  go d (NatM z s) = NatM (go d z) (go d s)
  go d (LstM n c) = LstM (go d n) (go d c)
  go d (EnuM cs e) = EnuM [(s, go d t) | (s, t) <- cs] (fmap (go d) e)
  go d (SigM f) = SigM (go d f)
  go d (EqlM f) = EqlM (go d f)
  go d (SupM l f) = SupM (go d l) (go d f)
  go d (Sup l a b) = Sup (go d l) (go d a) (go d b)
  go d (Eql t a b) = Eql (go d t) (go d a) (go d b)
  go d (Rwt e f) = Rwt (go d e) (go d f)
  go d (Frk l a b) = Frk (go d l) (go d a) (go d b)
  go d (Log s x) = Log (go d s) (go d x)
  go d (Met i t x) = Met i (go d t) (map (go d) x)
  go d t = t  -- All other terms remain unchanged

-- | Specialize cases in a pattern match
specializePatCases :: Int -> Book -> [Term] -> [Case] -> [Case]
specializePatCases d book [] cases = cases  -- No scrutinee, return as-is
specializePatCases d book (scrut:_) cases = 
  case findDefaultCase cases of
    Nothing -> cases  -- No default case, return as-is
    Just (defVar, defBody, otherCases) ->
      -- Try to infer type from scrutinee or existing cases
      case inferTypeFromCases book otherCases of
        Nothing -> cases  -- Can't infer type, return as-is
        Just typeName ->
          case getTypeConstructors book typeName of
            Nothing -> cases  -- Type not found, return as-is
            Just ctors ->
              let existingCtors = getExistingConstructors otherCases
                  missingCtors = filter (\(name, _) -> not (name `elem` existingCtors)) ctors
                  newCases = map (makeCase d defVar defBody) missingCtors
              in otherCases ++ newCases

-- | Find a default case (variable pattern) in the cases
findDefaultCase :: [Case] -> Maybe (String, Term, [Case])
findDefaultCase cases = go [] cases where
  go acc [] = Nothing
  go acc ((pats, body):rest) = 
    case pats of
      [pat] | isVarPattern pat -> 
        let varName = getVarName pat
        in Just (varName, body, acc ++ rest)
      _ -> go (acc ++ [(pats, body)]) rest
  
  isVarPattern (Var _ _) = True
  isVarPattern (Loc _ t) = isVarPattern t
  isVarPattern _ = False
  
  getVarName (Var n _) = n
  getVarName (Loc _ t) = getVarName t

-- | Infer type name from existing constructor cases
inferTypeFromCases :: Book -> [Case] -> Maybe String
inferTypeFromCases book@(Book defs _ typeCtors) cases = 
  findTypeFromConstructor (getFirstConstructor cases)
  where
    getFirstConstructor [] = Nothing
    getFirstConstructor ((pats, _):rest) = 
      case pats of
        [pat] -> extractConstructor pat
        _ -> getFirstConstructor rest
    
    extractConstructor :: Term -> Maybe String
    extractConstructor term = case term of
      Tup (Sym s) _ -> Just s  -- Pattern like (@E, ...)
      Tup (Loc _ (Sym s)) _ -> Just s  -- Pattern like (Loc ... @E, ...)
      Sym s -> Just s          -- Simple enum constructor
      Loc _ t -> extractConstructor t
      _ -> Nothing
    
    findTypeFromConstructor :: Maybe String -> Maybe String
    findTypeFromConstructor Nothing = Nothing
    findTypeFromConstructor (Just ctorName) = 
      M.foldlWithKey findType Nothing typeCtors
      where
        findType acc typeName ctors =
          case acc of
            Just _ -> acc
            Nothing -> if any (\(cname, _) -> cname == ctorName) ctors
                      then Just typeName
                      else Nothing

-- | Get list of existing constructor names from cases
-- After flattening, patterns are single-level, so we can simply extract all constructors
getExistingConstructors :: [Case] -> [String]
getExistingConstructors cases = concatMap extractFromCase cases where
  extractFromCase :: Case -> [String]
  extractFromCase (pats, _) = case pats of
    [pat] -> maybeToList (extractConstructor pat)
    _ -> []
  
  extractConstructor :: Term -> Maybe String
  extractConstructor term = case term of
    Tup (Sym s) _ -> Just s
    Tup (Loc _ (Sym s)) _ -> Just s  -- Handle located symbols
    Sym s -> Just s  -- Simple enum constructor
    Loc _ t -> extractConstructor t
    _ -> Nothing
  
  maybeToList Nothing = []
  maybeToList (Just x) = [x]

-- | Get type constructors from the book
getTypeConstructors :: Book -> String -> Maybe [(String, Int)]
getTypeConstructors (Book _ _ typeCtors) typeName = M.lookup typeName typeCtors

-- | Create a new case for a missing constructor
makeCase :: Int -> String -> Term -> (String, Int) -> Case
makeCase d defVar defBody (ctorName, arity) = 
  let pat = makePattern d ctorName arity
      reconstructed = makeReconstruction d ctorName arity
      body = Use defVar reconstructed (\_ -> defBody)
  in ([pat], body)

-- | Create the reconstruction term for use binding
makeReconstruction :: Int -> String -> Int -> Term
makeReconstruction d ctorName 0 = 
  -- No fields: (&Ctor, ())
  Tup (Sym ctorName) One
makeReconstruction d ctorName arity = 
  -- With fields: (&Ctor, field1, field2, ..., ())
  Tup (Sym ctorName) (makeFieldVars d arity)
  where
    makeFieldVars d 1 = Tup (Var ("_f" ++ show d) d) One
    makeFieldVars d n = Tup (Var ("_f" ++ show d) d) (makeFieldVars (d+1) (n-1))

-- | Create a pattern for a constructor with given arity
makePattern :: Int -> String -> Int -> Term
makePattern d ctorName 0 = 
  -- No fields: (&Ctor, ())
  Tup (Sym ctorName) One
makePattern d ctorName arity = 
  -- With fields: (&Ctor, field1, field2, ..., ())
  Tup (Sym ctorName) (makeFields d arity)
  where
    makeFields d 1 = Tup (Var ("_f" ++ show d) d) One
    makeFields d n = Tup (Var ("_f" ++ show d) d) (makeFields (d+1) (n-1))