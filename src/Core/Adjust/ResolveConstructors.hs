-- # Core.Adjust.ResolveConstructors
--
-- Resolves constructor names to their fully qualified names (FQNs).
-- This ensures that all constructors are globally unique by prefixing them
-- with their type's FQN (module::Type::Constructor).
--
-- Example:
--   Sym "Circle" in shapes.bend becomes Sym "shapes::Shape::Circle"
--
-- The resolution process:
-- 1. Extract all constructors from type definitions in the Book
-- 2. Build a map from unprefixed names to their FQNs
-- 3. Traverse all terms and resolve constructor references
-- 4. Error on ambiguous constructors, auto-prefix unique ones

module Core.Adjust.ResolveConstructors where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List (intercalate)
import Data.Maybe (fromMaybe)
import Control.Monad (foldM)
import Debug.Trace

import Core.Type
import Core.Show

-- | Map from unprefixed constructor name to list of possible FQNs
type ConstructorMap = M.Map String [String]

-- | Extract all constructors from a Book and build the constructor map
extractConstructors :: Book -> ConstructorMap
extractConstructors (Book defs _) = 
  M.foldrWithKey extractFromDefn M.empty defs
  where
    extractFromDefn :: Name -> Defn -> ConstructorMap -> ConstructorMap
    extractFromDefn typeName (_, term, _) cmap = 
      case term of
        -- Look for Enum type definitions
        Enu constructors -> 
          foldr (addConstructor typeName) cmap constructors
        -- Type definitions are often Sig types with Enu as the first component
        Sig (Enu constructors) _ ->
          foldr (addConstructor typeName) cmap constructors
        -- Also check in Loc wrappers
        Loc _ innerTerm -> 
          extractFromDefn typeName (True, innerTerm, Set) cmap
        _ -> cmap
    
    addConstructor :: Name -> String -> ConstructorMap -> ConstructorMap
    addConstructor typeFQN ctorName cmap =
      -- The constructor name might already be FQN (from parser), extract the base name
      let baseName = case reverse (splitOn "::" ctorName) of
            (base:_) -> base  -- Take the last part after ::
            [] -> ctorName
          -- For lookup, we use the base name
      in M.insertWith (++) baseName [ctorName] cmap
    
    splitOn :: String -> String -> [String]
    splitOn _ "" = []
    splitOn sep str = case breakOn sep str of
      (before, "") -> [before]
      (before, rest) -> before : splitOn sep (drop (length sep) rest)
    
    breakOn :: String -> String -> (String, String)
    breakOn sep str = go str ""
      where
        go [] acc = (reverse acc, "")
        go s@(c:cs) acc
          | sep `isPrefixOf` s = (reverse acc, s)
          | otherwise = go cs (c:acc)
        
        isPrefixOf [] _ = True
        isPrefixOf _ [] = False
        isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys

-- | Check if a constructor name is already fully qualified
isFullyQualified :: String -> Bool
isFullyQualified s = "::" `isInfixOf` s
  where
    isInfixOf needle haystack = any (isPrefixOf needle) (tails haystack)
    isPrefixOf [] _ = True
    isPrefixOf _ [] = False
    isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys
    tails [] = [[]]
    tails xs@(_:xs') = xs : tails xs'

-- | Resolve a single constructor name
resolveConstructor :: Span -> ConstructorMap -> String -> Result String
resolveConstructor span cmap ctorName =
  if isFullyQualified ctorName
  then Done ctorName  -- Already qualified, leave as-is
  else
    case M.lookup ctorName cmap of
      Nothing -> Done ctorName  -- Not a known constructor, leave as-is
      Just [fqn] -> Done fqn  -- Unique, auto-prefix
      Just fqns -> 
        -- Ambiguous constructor
        Fail $ AmbiguousConstructor span (Ctx []) ctorName fqns 
                 (Just $ "Please use one of: " ++ intercalate ", " (map ("&" ++) fqns))

-- | Resolve constructors in a term
resolveConstructorsInTerm :: ConstructorMap -> Term -> Result Term
resolveConstructorsInTerm cmap = go
  where
    go :: Term -> Result Term
    go term = case term of
      -- Constructor usage
      Sym name -> do
        resolved <- resolveConstructor noSpan cmap name
        Done (Sym resolved)
      
      -- Pattern matching on constructors
      EnuM cases def -> do
        resolvedCases <- mapM resolveCase cases
        resolvedDef <- go def
        Done (EnuM resolvedCases resolvedDef)
      
      -- Location wrapper
      Loc span innerTerm -> do
        -- Use the actual span for error reporting
        case innerTerm of
          Sym name -> do
            resolved <- resolveConstructor span cmap name
            Done (Loc span (Sym resolved))
          _ -> do
            resolved <- go innerTerm
            Done (Loc span resolved)
      
      -- Recursive cases
      Sub t -> Sub <$> go t
      Fix k f -> Done $ Fix k (\v -> case go (f v) of Done t -> t; Fail e -> error (show e))
      Let k t v f -> do
        t' <- mapM go t
        v' <- go v
        Done $ Let k t' v' (\u -> case go (f u) of Done t -> t; Fail e -> error (show e))
      Use k v f -> do
        v' <- go v
        Done $ Use k v' (\u -> case go (f u) of Done t -> t; Fail e -> error (show e))
      Chk x t -> Chk <$> go x <*> go t
      Tst x -> Tst <$> go x
      UniM f -> UniM <$> go f
      BitM f t -> BitM <$> go f <*> go t
      NatM z s -> NatM <$> go z <*> go s
      Lst t -> Lst <$> go t
      Con h t -> Con <$> go h <*> go t
      LstM n c -> LstM <$> go n <*> go c
      Op2 op a b -> Op2 op <$> go a <*> go b
      Op1 op a -> Op1 op <$> go a
      Sig a b -> Sig <$> go a <*> go b
      -- Special handling for constructor syntax @Ctor{...} which desugars to (Sym "Ctor", ...) or (Loc _ (Sym "Ctor"), ...)
      Tup (Sym name) rest -> do
        resolved <- resolveConstructor noSpan cmap name
        resolvedRest <- go rest
        Done (Tup (Sym resolved) resolvedRest)
      Tup (Loc span (Sym name)) rest -> do
        resolved <- resolveConstructor span cmap name
        resolvedRest <- go rest
        Done (Tup (Loc span (Sym resolved)) resolvedRest)
      Tup a b -> Tup <$> go a <*> go b
      SigM f -> SigM <$> go f
      All a b -> All <$> go a <*> go b
      Lam k t f -> do
        t' <- mapM go t
        Done $ Lam k t' (\u -> case go (f u) of Done t -> t; Fail e -> error (show e))
      App f x -> App <$> go f <*> go x
      Eql t a b -> Eql <$> go t <*> go a <*> go b
      EqlM f -> EqlM <$> go f
      Met n t ctx -> Met n <$> go t <*> mapM go ctx
      Sup l a b -> Sup <$> go l <*> go a <*> go b
      SupM l f -> SupM <$> go l <*> go f
      Log s x -> Log <$> go s <*> go x
      Rwt e f -> Rwt <$> go e <*> go f
      Pat s m c -> do
        s' <- mapM go s
        m' <- mapM (\(n, t) -> do t' <- go t; Done (n, t')) m
        c' <- mapM (\(ps, b) -> do ps' <- mapM go ps; b' <- go b; Done (ps', b')) c
        Done (Pat s' m' c')
      Frk l a b -> Frk <$> go l <*> go a <*> go b
      
      -- Leaf nodes that don't contain constructors
      Var _ _ -> Done term
      Ref _ _ -> Done term
      Set -> Done term
      Emp -> Done term
      EmpM -> Done term
      Uni -> Done term
      One -> Done term
      Bit -> Done term
      Bt0 -> Done term
      Bt1 -> Done term
      Nat -> Done term
      Zer -> Done term
      Suc n -> Suc <$> go n
      Nil -> Done term
      Enu cs -> Done term  -- Type definition, not usage
      Num n -> Done term
      Val v -> Done term
      Rfl -> Done term
      Era -> Done term
      Pri p -> Done term
    
    resolveCase :: (String, Term) -> Result (String, Term)
    resolveCase (ctorName, body) = do
      resolvedCtor <- resolveConstructor noSpan cmap ctorName
      resolvedBody <- go body
      Done (resolvedCtor, resolvedBody)

-- | Resolve constructors in a definition
resolveConstructorsInDefn :: ConstructorMap -> Defn -> Result Defn
resolveConstructorsInDefn cmap (inj, term, typ) = do
  resolvedTerm <- resolveConstructorsInTerm cmap term
  resolvedType <- resolveConstructorsInTerm cmap typ
  Done (inj, resolvedTerm, resolvedType)

-- | Resolve constructors in an entire Book
resolveConstructorsInBook :: Book -> Result Book
resolveConstructorsInBook book@(Book defs names) = do
  let cmap = extractConstructors book
  resolvedDefs <- M.traverseWithKey (\_ defn -> resolveConstructorsInDefn cmap defn) defs
  Done (Book resolvedDefs names)