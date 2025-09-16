-- Resolves Enums names to their fully qualified names (FQNs).
-- This ensures that all enums are globally unique by prefixing them
-- with their type's FQN (module::Type::Enum).
--
-- Example:
--   Sym "Circle" fields in shapes.bend becomes Sym "shapes::Shape::Circle" fields
--
-- The resolution process:
-- 1. Extract all enum from type definitions in the Book
-- 2. Build a map from unprefixed names to their FQNs
-- 3. Traverse all terms and resolve enum references
-- 4. Error on ambiguous enums, auto-prefix unique ones

module Core.Adjust.ResolveEnums where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List (intercalate, isPrefixOf)
import Data.List.Split (splitOn)
import Data.Maybe (fromMaybe)
import Control.Monad (foldM)

import Core.Type
import Core.Show

-- | Map from unprefixed enum name to list of possible FQNs
type EnumMap = M.Map String [String]

-- | Extract all enums from a Book and build the enum map
extractEnums :: Book -> EnumMap
extractEnums (Book defs _) =
  M.foldrWithKey extractFromDefn M.empty defs
  where
    extractFromDefn :: Name -> Defn -> EnumMap -> EnumMap
    extractFromDefn typeName (_, term, _) emap =
      case term of
        -- Look for Enum type definitions
        Enu enums ->
          foldr (addEnum typeName) emap enums
        -- Type definitions are often Sig types with Enu as the first component
        Sig (Enu enums) _ ->
          foldr (addEnum typeName) emap enums
        -- Also check in Loc wrappers
        Loc _ innerTerm ->
          extractFromDefn typeName (True, innerTerm, Set) emap
        -- Check in All (forall) types for generic types
        All _ body ->
          extractFromDefn typeName (True, body, Set) emap
        -- Check in Lam for parameterized types like Result<F,D>
        Lam _ _ body ->
          -- The body is a function, we need to apply it to extract the actual type
          -- For now, let's just explore the body recursively
          extractFromDefn typeName (True, body (Var "dummy" 0), Set) emap
        _ -> emap
    
    addEnum :: Name -> String -> EnumMap -> EnumMap
    addEnum typeFQN enumName emap =
      -- The enum name might already be FQN (from parser), extract the base name
      let baseName = case reverse (splitOn "::" enumName) of
            (base:_) -> base  -- Take the last part after ::
            [] -> enumName
          -- For lookup, we use the base name
      in M.insertWith (++) baseName [enumName] emap

-- | Check if an enum name is already fully qualified
isFullyQualified :: String -> Bool
isFullyQualified s = "::" `isInfixOf` s
  where
    isInfixOf needle haystack = any (isPrefixOf needle) (tails haystack)
    isPrefixOf [] _ = True
    isPrefixOf _ [] = False
    isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys
    tails [] = [[]]
    tails xs@(_:xs') = xs : tails xs'

-- | Resolve a single enum name
resolveEnum :: Span -> EnumMap -> String -> Result String
resolveEnum span emap enumName =
  if isFullyQualified enumName
  then Done enumName  -- Already qualified, leave as-is
  else
    case M.lookup enumName emap of
      Nothing -> Done enumName  -- Not a known enum, leave as-is
      Just [fqn] -> Done fqn    -- Unique, auto-prefix
      Just fqns ->
        -- Ambiguous Enum
        Fail $ AmbiguousEnum span (Ctx []) enumName fqns
                 (Just $ "Please use one of: " ++ intercalate ", " (map ("&" ++) fqns))

-- | Resolve enums in a term
resolveEnumsInTerm :: EnumMap -> Term -> Result Term
resolveEnumsInTerm emap = go
  where
    go :: Term -> Result Term
    go term = case term of
      -- Enum usage
      Sym name -> do
        resolved <- resolveEnum noSpan emap name
        Done (Sym resolved)
      
      -- Pattern matching on Enums
      EnuM cases def -> do
        resolvedCases <- mapM resolveCase cases
        resolvedDef <- go def
        Done (EnuM resolvedCases resolvedDef)
      
      -- Location wrapper
      Loc span innerTerm -> do
        -- Use the actual span for error reporting
        case innerTerm of
          Sym name -> do
            resolved <- resolveEnum span emap name
            Done (Loc span (Sym resolved))
          _ -> do
            resolved <- go innerTerm
            Done (Loc span resolved)
      
      -- Recursive cases
      Sub t -> do
        t2 <- go t
        Done (Sub t2)
      Fix k f -> Done $ Fix k (\v -> case go (f v) of Done t -> t; Fail e -> error (show e))
      Let k t v f -> do
        t2 <- mapM go t
        v2 <- go v
        Done $ Let k t2 v2 (\u -> case go (f u) of Done t -> t; Fail e -> error (show e))
      Use k v f -> do
        v2 <- go v
        Done $ Use k v2 (\u -> case go (f u) of Done t -> t; Fail e -> error (show e))
      Chk x t -> do
        x2 <- go x
        t2 <- go t
        Done (Chk x2 t2)
      Tst x -> do
        x2 <- go x
        Done (Tst x2)
      UniM f -> do
        f2 <- go f
        Done (UniM f2)
      BitM f t -> do
        f2 <- go f
        t2 <- go t
        Done (BitM f2 t2)
      NatM z s -> do
        z2 <- go z
        s2 <- go s
        Done (NatM z2 s2)
      Lst t -> do
        t2 <- go t
        Done (Lst t2)
      Con h t -> do
        h2 <- go h
        t2 <- go t
        Done (Con h2 t2)
      LstM n c -> do
        n2 <- go n
        c2 <- go c
        Done (LstM n2 c2)
      Op2 op a b -> do
        a2 <- go a
        b2 <- go b
        Done (Op2 op a2 b2)
      Op1 op a -> do
        a2 <- go a
        Done (Op1 op a2)
      Sig a b -> do
        a2 <- go a
        b2 <- go b
        Done (Sig a2 b2)
      -- Special handling for enum syntax @Enum{...} which desugars to (Sym "Enum", ...) or (Loc _ (Sym "Enum"), ...)
      Tup (Sym name) rest -> do
        resolved <- resolveEnum noSpan emap name
        resolvedRest <- go rest
        Done (Tup (Sym resolved) resolvedRest)
      Tup (Loc span (Sym name)) rest -> do
        resolved <- resolveEnum span emap name
        resolvedRest <- go rest
        Done (Tup (Loc span (Sym resolved)) resolvedRest)
      Tup a b -> do
        a2 <- go a
        b2 <- go b
        Done (Tup a2 b2)
      SigM f -> do
        f2 <- go f
        Done (SigM f2)
      All a b -> do
        a2 <- go a
        b2 <- go b
        Done (All a2 b2)
      Lam k t f -> do
        t2 <- mapM go t
        Done $ Lam k t2 (\u -> case go (f u) of Done t -> t; Fail e -> error (show e))
      App f x -> do
        f2 <- go f
        x2 <- go x
        Done (App f2 x2)
      Eql t a b -> do
        t2 <- go t
        a2 <- go a
        b2 <- go b
        Done (Eql t2 a2 b2)
      EqlM f -> do
        f2 <- go f
        Done (EqlM f2)
      Met n t ctx -> do
        t2 <- go t
        ctx2 <- mapM go ctx
        Done (Met n t2 ctx2)
      Sup l a b -> do
        l2 <- go l
        a2 <- go a
        b2 <- go b
        Done (Sup l2 a2 b2)
      SupM l f -> do
        l2 <- go l
        f2 <- go f
        Done (SupM l2 f2)
      Log s x -> do
        s2 <- go s
        x2 <- go x
        Done (Log s2 x2)
      Rwt e f -> do
        e2 <- go e
        f2 <- go f
        Done (Rwt e2 f2)
      Pat s m c -> do
        s2 <- mapM go s
        m2 <- mapM (\(n, t) -> do t2 <- go t; Done (n, t2)) m
        c2 <- mapM (\(ps, b) -> do ps2 <- mapM go ps; b2 <- go b; Done (ps2, b2)) c
        Done (Pat s2 m2 c2)
      Frk l a b -> do
        l2 <- go l
        a2 <- go a
        b2 <- go b
        Done (Frk l2 a2 b2)
      
      -- Leaf nodes that don't contain Enums
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
      Suc n -> do
        n2 <- go n
        Done (Suc n2)
      Nil -> Done term
      Enu cs -> Done term  -- Type definition, not usage
      Num n -> Done term
      Val v -> Done term
      Rfl -> Done term
      Era -> Done term
      Pri p -> Done term
    
    resolveCase :: (String, Term) -> Result (String, Term)
    resolveCase (enumName, body) = do
      resolvedEnum <- resolveEnum noSpan emap enumName
      resolvedBody <- go body
      Done (resolvedEnum, resolvedBody)

-- | Resolve enums in a definition
resolveEnumsInDefn :: EnumMap -> Defn -> Result Defn
resolveEnumsInDefn emap (inj, term, typ) = do
  resolvedTerm <- resolveEnumsInTerm emap term
  resolvedType <- resolveEnumsInTerm emap typ
  Done (inj, resolvedTerm, resolvedType)

-- | Resolve enums in an entire Book
resolveEnumsInBook :: Book -> Result Book
resolveEnumsInBook book@(Book defs names) = do
  let emap = extractEnums book
  resolvedDefs <- M.traverseWithKey (\_ defn -> resolveEnumsInDefn emap defn) defs
  Done (Book resolvedDefs names)
