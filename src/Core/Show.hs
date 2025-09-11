{-./Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Show where

import Core.Type
import Data.List (intercalate, unsnoc, isInfixOf)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M
import qualified Data.Set as S
import Highlight (highlightError)

import System.Exit
import System.IO
import System.IO.Unsafe (unsafePerformIO)

-- Term Display
-- ============

-- | Main entry point for term display with optional depth tracking and FQN display
showTerm :: Bool -> Bool -> Term -> String
showTerm showFQN trackDepth term = case showFQN of
  True  -> showPlain S.empty S.empty term 0 True  -- Show full FQNs
  False -> case trackDepth of
    True  -> showWithShadowing term
    False -> showWithoutPrefixes term

-- | Show terms with depth annotations for shadowed variables only
showWithShadowing :: Term -> String
showWithShadowing term = case S.null shadowed of
  True  -> showPlain S.empty S.empty term 0 False
  False -> showPlain shadowed S.empty adjusted 0 False
  where
    shadowed = getShadowed term
    adjusted = adjustDepths term 0

-- | Show terms without module prefixes (unless ambiguous)
showWithoutPrefixes :: Term -> String
showWithoutPrefixes term = showPlain S.empty ambiguous term 0 False
  where
    ambiguous = getAmbiguousNames term

showPlain :: S.Set String -> S.Set String -> Term -> Int -> Bool -> String
showPlain shadowed ambiguous term depth showFQN = case term of
  -- Variables
  Var k i      -> showVar shadowed k i
  Ref k i      -> if showFQN then k else stripPrefix ambiguous k
  Sub t        -> showPlain shadowed ambiguous t depth showFQN

  -- Binding forms
  Fix k f      -> showFix shadowed ambiguous k f depth showFQN
  Let k t v f  -> showLet shadowed ambiguous k t v f depth showFQN
  Use k v f    -> showUse shadowed ambiguous k v f depth showFQN

  -- Types and annotations
  Set          -> "Set"
  Chk x t      -> "(" ++ showPlain shadowed ambiguous x depth showFQN ++ "::" ++ showPlain shadowed ambiguous t depth showFQN ++ ")"
  Tst x        -> "trust " ++ showPlain shadowed ambiguous x depth showFQN

  -- Empty
  Emp          -> "Empty"
  EmpM         -> "λ{}"

  -- Unit
  Uni          -> "Unit"
  One          -> "()"
  UniM f       -> "λ{():" ++ showPlain shadowed ambiguous f depth showFQN ++ "}"

  -- Bool
  Bit          -> "Bool"
  Bt0          -> "False"
  Bt1          -> "True"
  BitM f t     -> "λ{False:" ++ showPlain shadowed ambiguous f depth showFQN ++ ";True:" ++ showPlain shadowed ambiguous t depth showFQN ++ "}"

  -- Nat
  Nat          -> "Nat"
  Zer          -> "0n"
  Suc _        -> showSuc shadowed ambiguous term depth showFQN
  NatM z s     -> "λ{0n:" ++ showPlain shadowed ambiguous z depth showFQN ++ ";1n+:" ++ showPlain shadowed ambiguous s depth showFQN ++ "}"

  -- List
  Lst t        -> showPlain shadowed ambiguous t depth showFQN ++ "[]"
  Nil          -> "[]"
  Con h t      -> showCon shadowed ambiguous h t depth showFQN
  LstM n c     -> "λ{[]:" ++ showPlain shadowed ambiguous n depth showFQN ++ ";<>:" ++ showPlain shadowed ambiguous c depth showFQN ++ "}"

  -- Enum
  Enu s        -> "enum{" ++ intercalate "," (map ("&" ++) s) ++ "}"
  Sym s        -> "&" ++ (if showFQN then s else stripPrefix ambiguous s)
  EnuM cs d    -> showEnuM shadowed ambiguous cs d depth showFQN

  -- Pair
  Sig a b      -> showSig shadowed ambiguous a b depth showFQN
  Tup _ _      -> showTup shadowed ambiguous term depth showFQN  
  SigM f       -> "λ{(,):" ++ showPlain shadowed ambiguous f depth showFQN ++ "}"

  -- Function
  All a b      -> showAll shadowed ambiguous a b depth showFQN
  Lam k t f    -> showLam shadowed ambiguous k t f depth showFQN
  App _ _      -> showApp shadowed ambiguous term depth showFQN

  -- Equality
  Eql t a b    -> showEql shadowed ambiguous t a b depth showFQN
  Rfl          -> "{==}"
  EqlM f       -> "λ{{==}:" ++ showPlain shadowed ambiguous f depth showFQN ++ "}"
  Rwt e f      -> "rewrite " ++ showPlain shadowed ambiguous e depth showFQN ++ " " ++ showPlain shadowed ambiguous f depth showFQN

  -- Meta and superposition
  Met n t ctx  -> "?" ++ n ++ ":" ++ showPlain shadowed ambiguous t depth showFQN ++ "{" ++ intercalate "," (map (\c -> showPlain shadowed ambiguous c depth showFQN) ctx) ++ "}"
  Era          -> "*"
  Sup l a b    -> "&" ++ showPlain shadowed ambiguous l depth showFQN ++ "{" ++ showPlain shadowed ambiguous a depth showFQN ++ "," ++ showPlain shadowed ambiguous b depth showFQN ++ "}"
  SupM l f     -> "λ{&" ++ showPlain shadowed ambiguous l depth showFQN ++ "{,}:" ++ showPlain shadowed ambiguous f depth showFQN ++ "}"

  -- Location and logging
  Loc _ t      -> showPlain shadowed ambiguous t depth showFQN
  Log s x      -> "log " ++ showPlain shadowed ambiguous s depth showFQN ++ " " ++ showPlain shadowed ambiguous x depth showFQN

  -- Primitives
  Pri p        -> showPri p
  Num t        -> showNum t
  Val v        -> showVal v
  Op2 o a b    -> showOp2 shadowed ambiguous o a b depth showFQN
  Op1 o a      -> showOp1 shadowed ambiguous o a depth showFQN

  -- Patterns
  Pat ts ms cs -> showPat shadowed ambiguous ts ms cs depth showFQN
  Frk l a b    -> "fork " ++ showPlain shadowed ambiguous l depth showFQN ++ ":" ++ showPlain shadowed ambiguous a depth showFQN ++ " else:" ++ showPlain shadowed ambiguous b depth showFQN

-- Helper functions for complex cases
-- ==================================

-- | Show variable with depth annotation if shadowed: x or x^2
showVar :: S.Set String -> String -> Int -> String
showVar shadowed k i = case S.member k shadowed of
  True  -> k ++ "^" ++ show i
  False -> k

-- | μx. body
showFix :: S.Set String -> S.Set String -> String -> Body -> Int -> Bool -> String
showFix shadowed ambiguous k f depth showFQN = "μ" ++ kStr ++ ". " ++ showPlain shadowed ambiguous (f (Var k depth)) (depth + 1) showFQN
  where kStr = varName shadowed k depth

-- | x : T = v body or x = v body
showLet :: S.Set String -> S.Set String -> String -> Maybe Term -> Term -> Body -> Int -> Bool -> String
showLet shadowed ambiguous k t v f depth showFQN = case t of
  Just t  -> kStr ++ " : " ++ showPlain shadowed ambiguous t depth showFQN ++ " = " ++ showPlain shadowed ambiguous v depth showFQN ++ " " ++ showPlain shadowed ambiguous (f (Var k depth)) (depth + 1) showFQN
  Nothing -> kStr ++ " = " ++ showPlain shadowed ambiguous v depth showFQN ++ " " ++ showPlain shadowed ambiguous (f (Var k depth)) (depth + 1) showFQN
  where kStr = varName shadowed k depth

-- | use x = v body
showUse :: S.Set String -> S.Set String -> String -> Term -> Body -> Int -> Bool -> String
showUse shadowed ambiguous k v f depth showFQN = "use " ++ varName shadowed k depth ++ " = " ++ showPlain shadowed ambiguous v depth showFQN ++ " " ++ showPlain shadowed ambiguous (f (Var k depth)) (depth + 1) showFQN

-- | Count successor applications: 3n or 2n+x
showSuc :: S.Set String -> S.Set String -> Term -> Int -> Bool -> String
showSuc shadowed ambiguous term depth showFQN = case count term of
  (k, Zer) -> show (k :: Integer) ++ "n"
  (k, r)   -> show (k :: Integer) ++ "n+" ++ showPlain shadowed ambiguous r depth showFQN
  where
    count (cut -> Suc t) = let (c, r) = count t in (c + 1, r)
    count t              = (0 :: Integer, t)

-- | List constructor: h<>t or "string" for character lists
showCon :: S.Set String -> S.Set String -> Term -> Term -> Int -> Bool -> String
showCon shadowed ambiguous h t depth showFQN = fromMaybe plain (showStr shadowed ambiguous (Con h t) depth showFQN)
  where plain = showPlain shadowed ambiguous h depth showFQN ++ "<>" ++ showPlain shadowed ambiguous t depth showFQN

-- | Enum matcher: λ{&foo:x;&bar:y;default}
showEnuM :: S.Set String -> S.Set String -> [(String,Term)] -> Term -> Int -> Bool -> String
showEnuM shadowed ambiguous cs d depth showFQN = "λ{" ++ intercalate ";" cases ++ ";" ++ showPlain shadowed ambiguous d depth showFQN ++ "}"
  where cases = map (\(s,t) -> "&" ++ (if showFQN then s else stripPrefix ambiguous s) ++ ":" ++ showPlain shadowed ambiguous t depth showFQN) cs

-- | Dependent pair type: Σx:A. B or A & B
showSig :: S.Set String -> S.Set String -> Term -> Term -> Int -> Bool -> String
showSig shadowed ambiguous a b depth showFQN = case cut b of
  Lam "_" t f -> "(" ++ showArg a ++ " & " ++ showCodomain (f (Var "_" depth)) ++ ")"
  Lam k t f   -> "Σ" ++ varName shadowed k depth ++ ":" ++ showArg a ++ ". " ++ showPlain shadowed ambiguous (f (Var k depth)) (depth + 1) showFQN
  _           -> "Σ" ++ showArg a ++ ". " ++ showPlain shadowed ambiguous b depth showFQN
  where
    showArg t = case cut t of
      All{} -> "(" ++ showPlain shadowed ambiguous t depth showFQN ++ ")"
      Sig{} -> "(" ++ showPlain shadowed ambiguous t depth showFQN ++ ")"
      _     -> showPlain shadowed ambiguous t depth showFQN
    showCodomain t = case t of
      Sig _ (Lam k _ _) | k /= "_" -> "(" ++ showPlain shadowed ambiguous t (depth + 1) showFQN ++ ")"
      _                           -> showPlain shadowed ambiguous t (depth + 1) showFQN

-- | Dependent function type: ∀x:A. B or A -> B
showAll :: S.Set String -> S.Set String -> Term -> Term -> Int -> Bool -> String
showAll shadowed ambiguous a b depth showFQN = case b of
  Lam "_" t f -> showArg a ++ " -> " ++ showCodomain (f (Var "_" depth))
  Lam k t f   -> "∀" ++ varName shadowed k depth ++ ":" ++ showArg a ++ ". " ++ showPlain shadowed ambiguous (f (Var k depth)) (depth + 1) showFQN
  _           -> "∀" ++ showArg a ++ ". " ++ showPlain shadowed ambiguous b depth showFQN
  where
    showArg t = case cut t of
      All{} -> "(" ++ showPlain shadowed ambiguous t depth showFQN ++ ")"
      Sig{} -> "(" ++ showPlain shadowed ambiguous t depth showFQN ++ ")"
      _     -> showPlain shadowed ambiguous t depth showFQN
    showCodomain t = case t of
      All _ (Lam k _ _) | k /= "_" -> "(" ++ showPlain shadowed ambiguous t (depth + 1) showFQN ++ ")"
      _                           -> showPlain shadowed ambiguous t (depth + 1) showFQN

-- | Lambda abstraction: λx:T. body or λx. body
showLam :: S.Set String -> S.Set String -> String -> Maybe Term -> Body -> Int -> Bool -> String
showLam shadowed ambiguous k t f depth showFQN = case t of
  Just t  -> "λ" ++ varName shadowed k depth ++ ":" ++ showPlain shadowed ambiguous t depth showFQN ++ ". " ++ showPlain shadowed ambiguous (f (Var k depth)) (depth + 1) showFQN
  Nothing -> "λ" ++ varName shadowed k depth ++ ". " ++ showPlain shadowed ambiguous (f (Var k depth)) (depth + 1) showFQN

-- | Function application: f(x,y,z)
showApp :: S.Set String -> S.Set String -> Term -> Int -> Bool -> String
showApp shadowed ambiguous term depth showFQN = fnStr ++ "(" ++ intercalate "," (map (\arg -> showPlain shadowed ambiguous arg depth showFQN) args) ++ ")"
  where 
    (fn, args) = collectApps term []
    fnStr = case cut fn of
      Var k i -> showVar shadowed k i
      Ref k i -> if showFQN then k else stripPrefix ambiguous k  
      _       -> "(" ++ showPlain shadowed ambiguous fn depth showFQN ++ ")"

-- | Tuple: (a,b,c) or @Ctor{a,b}
showTup :: S.Set String -> S.Set String -> Term -> Int -> Bool -> String
showTup shadowed ambiguous term depth showFQN = fromMaybe plain (showCtr ambiguous term showFQN)
  where plain = "(" ++ intercalate "," (map (\t -> showPlain shadowed ambiguous t depth showFQN) (flattenTup term)) ++ ")"

-- | Equality type: T{a == b}
showEql :: S.Set String -> S.Set String -> Term -> Term -> Term -> Int -> Bool -> String  
showEql shadowed ambiguous t a b depth showFQN = typeStr ++ "{" ++ showPlain shadowed ambiguous a depth showFQN ++ "==" ++ showPlain shadowed ambiguous b depth showFQN ++ "}"
  where 
    typeStr = case t of
      Sig _ _ -> "(" ++ showPlain shadowed ambiguous t depth showFQN ++ ")"
      All _ _ -> "(" ++ showPlain shadowed ambiguous t depth showFQN ++ ")"
      _      -> showPlain shadowed ambiguous t depth showFQN

-- | Binary operator: (a + b)
showOp2 :: S.Set String -> S.Set String -> NOp2 -> Term -> Term -> Int -> Bool -> String
showOp2 shadowed ambiguous op a b depth showFQN = "(" ++ showPlain shadowed ambiguous a depth showFQN ++ " " ++ opStr ++ " " ++ showPlain shadowed ambiguous b depth showFQN ++ ")"
  where
    opStr = case op of
      ADD -> "+";   SUB -> "-";   MUL -> "*";   DIV -> "/"
      MOD -> "%";   POW -> "**";  EQL -> "==";  NEQ -> "!==" 
      LST -> "<";   GRT -> ">";   LEQ -> "<=";  GEQ -> ">="
      AND -> "&&";  OR  -> "|";   XOR -> "^"
      SHL -> "<<";  SHR -> ">>"

-- | Unary operator: (not a) or (-a)
showOp1 :: S.Set String -> S.Set String -> NOp1 -> Term -> Int -> Bool -> String
showOp1 shadowed ambiguous op a depth showFQN = case op of
  NOT -> "(not " ++ showPlain shadowed ambiguous a depth showFQN ++ ")"
  NEG -> "(-" ++ showPlain shadowed ambiguous a depth showFQN ++ ")"

-- | Pattern match: match x { with k=v case (p): body }
showPat :: S.Set String -> S.Set String -> [Term] -> [Move] -> [Case] -> Int -> Bool -> String
showPat shadowed ambiguous ts ms cs depth showFQN = "match " ++ unwords (map (\t -> showPlain shadowed ambiguous t depth showFQN) ts) ++ " {" ++ moves ++ cases ++ " }"
  where
    moves = case ms of
      [] -> ""
      _  -> " with " ++ intercalate " with " (map showMove ms)
    cases = case cs of  
      [] -> ""
      _  -> " " ++ intercalate " " (map showCase cs)
    showMove (k,x) = k ++ "=" ++ showPlain shadowed ambiguous x depth showFQN
    showCase (ps,x) = "case " ++ unwords (map showPat' ps) ++ ": " ++ showPlain shadowed ambiguous x depth showFQN
    showPat' p = "(" ++ showPlain shadowed ambiguous p depth showFQN ++ ")"

-- Primitive display
-- =================

showPri :: PriF -> String
showPri p = case p of
  U64_TO_CHAR -> "U64_TO_CHAR"
  CHAR_TO_U64 -> "CHAR_TO_U64" 
  HVM_INC     -> "HVM_INC"
  HVM_DEC     -> "HVM_DEC"

showNum :: NTyp -> String
showNum t = case t of
  U64_T -> "U64"
  I64_T -> "I64" 
  F64_T -> "F64"
  CHR_T -> "Char"

showVal :: NVal -> String
showVal v = case v of
  U64_V n -> show n
  I64_V n -> case n >= 0 of
    True  -> "+" ++ show n
    False -> show n
  F64_V n -> show n
  CHR_V c -> "'" ++ Core.Show.showChar c ++ "'"

showChar :: Char -> String
showChar c = case c of
  '\n' -> "\\n";  '\t' -> "\\t";  '\r' -> "\\r";  '\0' -> "\\0"
  '\\' -> "\\\\"; '\'' -> "\\'"
  _    -> [c]

-- String display helpers
-- ======================

-- | Try to display character list as string literal: "hello"
showStr :: S.Set String -> S.Set String -> Term -> Int -> Bool -> Maybe String  
showStr shadowed ambiguous term depth showFQN = go [] term
  where
    go acc Nil                        = Just ("\"" ++ reverse acc ++ "\"")
    go acc (Con (Val (CHR_V c)) rest) = go (c:acc) rest
    go acc (Loc _ t)                  = go acc t
    go _   _                          = Nothing

-- | Try to display tuple as constructor: @Ctor{a,b}
showCtr :: S.Set String -> Term -> Bool -> Maybe String
showCtr ambiguous t showFQN =
  let ts = map cut (flattenTup t) in
  case unsnoc ts of
    Just ((Sym name : ts), One) -> Just ("@" ++ (if showFQN then name else stripPrefix ambiguous name) ++ "{" ++ intercalate "," (map show ts) ++ "}")
    _                           -> Nothing

-- Utility functions
-- =================

-- | Strip module prefix from a name unless it's ambiguous
stripPrefix :: S.Set String -> String -> String
stripPrefix ambiguous name = 
  let unqualified = extractUnqualifiedName name
  in if unqualified `S.member` ambiguous
     then name  -- Keep full name if ambiguous
     else unqualified

-- | Extract unqualified name from a fully qualified name
-- "Nat/add::Nat/add" -> "Nat/add"
-- "Bool::True" -> "True"
-- "foo" -> "foo"
extractUnqualifiedName :: String -> String
extractUnqualifiedName name = 
  case reverse (splitOn "::" name) of
    (last:_) -> last
    []       -> name
  where
    splitOn :: String -> String -> [String]
    splitOn delim str = go "" str
      where
        go :: String -> String -> [String]
        go acc [] = if null acc then [] else [reverse acc]
        go acc s@(c:cs)
          | delim `isPrefixOf` s = 
              if null acc 
              then go "" (drop (length delim) s)
              else reverse acc : go "" (drop (length delim) s)
          | otherwise = go (c:acc) cs
    
    isPrefixOf :: Eq a => [a] -> [a] -> Bool
    isPrefixOf [] _ = True
    isPrefixOf _ [] = False
    isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys

-- | Collect all qualified names and detect ambiguities
getAmbiguousNames :: Term -> S.Set String
getAmbiguousNames term = 
  let allNames = collectQualifiedNames term
      nameMap = buildNameMap allNames
      ambiguous = findAmbiguous nameMap
  in ambiguous
  where
    -- Build a map from unqualified names to their qualified versions
    buildNameMap :: S.Set String -> M.Map String (S.Set String)
    buildNameMap names = S.foldr addName M.empty names
      where
        addName :: String -> M.Map String (S.Set String) -> M.Map String (S.Set String)
        addName qualifiedName acc = 
          let unqualified = extractUnqualifiedName qualifiedName
          in M.insertWith S.union unqualified (S.singleton qualifiedName) acc
    
    -- Find unqualified names that map to multiple qualified names
    findAmbiguous :: M.Map String (S.Set String) -> S.Set String
    findAmbiguous nameMap = 
      M.keysSet $ M.filter (\qualifieds -> S.size qualifieds > 1) nameMap

-- | Collect all qualified names (Refs and Syms) from a term
collectQualifiedNames :: Term -> S.Set String
collectQualifiedNames = go S.empty
  where
    go :: S.Set String -> Term -> S.Set String
    go bound term = case term of
      Ref k _ -> if "::" `isInfixOf` k then S.insert k bound else bound
      Sym s -> if "::" `isInfixOf` s then S.insert s bound else bound
      
      -- Traverse all subterms
      Sub t -> go bound t
      Fix _ f -> go bound (f (Var "_dummy" 0))
      Let _ t v f -> go (maybe bound (go bound) t) v `S.union` go bound (f (Var "_dummy" 0))
      Use _ v f -> go bound v `S.union` go bound (f (Var "_dummy" 0))
      Chk x t -> go bound x `S.union` go bound t
      Tst x -> go bound x
      UniM f -> go bound f
      BitM f t -> go bound f `S.union` go bound t
      NatM z s -> go bound z `S.union` go bound s
      Suc n -> go bound n
      Lst t -> go bound t
      Con h t -> go bound h `S.union` go bound t
      LstM n c -> go bound n `S.union` go bound c
      EnuM cs d -> S.unions (map (go bound . snd) cs) `S.union` go bound d
      Op2 _ a b -> go bound a `S.union` go bound b
      Op1 _ a -> go bound a
      Sig a b -> go bound a `S.union` go bound b
      Tup a b -> go bound a `S.union` go bound b
      SigM f -> go bound f
      All a b -> go bound a `S.union` go bound b
      Lam _ t f -> maybe (go bound (f (Var "_dummy" 0))) (\t' -> go bound t' `S.union` go bound (f (Var "_dummy" 0))) t
      App f a -> go bound f `S.union` go bound a
      Eql t a b -> go bound t `S.union` go bound a `S.union` go bound b
      EqlM f -> go bound f
      Rwt e f -> go bound e `S.union` go bound f
      Met _ t ctx -> go bound t `S.union` S.unions (map (go bound) ctx)
      Sup l a b -> go bound l `S.union` go bound a `S.union` go bound b
      SupM l f -> go bound l `S.union` go bound f
      Loc _ t -> go bound t
      Log s x -> go bound s `S.union` go bound x
      Pat ts ms cs -> S.unions (map (go bound) ts) `S.union` 
                     S.unions (map (go bound . snd) ms) `S.union`
                     S.unions [S.unions (map (go bound) ps) `S.union` go bound b | (ps, b) <- cs]
      Frk l a b -> go bound l `S.union` go bound a `S.union` go bound b
      _ -> S.empty

-- | Add depth suffix to variable name if shadowed
varName :: S.Set String -> String -> Int -> String
varName shadowed k depth = case S.member k shadowed of
  True  -> k ++ "^" ++ show depth
  False -> k

-- Depth tracking for shadowing
-- ============================

-- | Find variable names that are shadowed (appear at multiple depths)
getShadowed :: Term -> S.Set String
getShadowed term = S.fromList [k | (k, _) <- duplicates]
  where
    adjusted = adjustDepths term 0
    vars = collectVars adjusted
    duplicates = findDups vars
    
    findDups vars = [(k, ds) | (k, ds) <- uniqueDepths, length ds > 1]
      where
        grouped = M.toList $ M.fromListWith (++) [(k, [i]) | (k, i) <- vars]
        uniqueDepths = [(k, S.toList $ S.fromList is) | (k, is) <- grouped]

-- | Replace HOAS bindings with depth-indexed variables for shadowing analysis
adjustDepths :: Term -> Int -> Term
adjustDepths term depth = case term of
  Var k i    -> Var k i
  Ref k i    -> Ref k i  
  Sub t      -> Sub (adjustDepths t depth)
  Fix k f    -> Fix k (\x -> adjustDepths (f (Var k depth)) (depth + 1))
  Let k t v f -> Let k (fmap (\t' -> adjustDepths t' depth) t) (adjustDepths v depth) (\x -> adjustDepths (f (Var k depth)) (depth + 1))
  Use k v f  -> Use k (adjustDepths v depth) (\x -> adjustDepths (f (Var k depth)) (depth + 1))
  Set        -> Set
  Chk x t    -> Chk (adjustDepths x depth) (adjustDepths t depth)
  Tst x      -> Tst (adjustDepths x depth)
  Emp        -> Emp
  EmpM       -> EmpM
  Uni        -> Uni
  One        -> One
  UniM f     -> UniM (adjustDepths f depth)
  Bit        -> Bit
  Bt0        -> Bt0
  Bt1        -> Bt1
  BitM f t   -> BitM (adjustDepths f depth) (adjustDepths t depth)
  Nat        -> Nat
  Zer        -> Zer
  Suc n      -> Suc (adjustDepths n depth)
  NatM z s   -> NatM (adjustDepths z depth) (adjustDepths s depth)
  Lst t      -> Lst (adjustDepths t depth)
  Nil        -> Nil
  Con h t    -> Con (adjustDepths h depth) (adjustDepths t depth)
  LstM n c   -> LstM (adjustDepths n depth) (adjustDepths c depth)
  Enu s      -> Enu s
  Sym s      -> Sym s
  EnuM cs d  -> EnuM [(s, adjustDepths t depth) | (s, t) <- cs] (adjustDepths d depth)
  Num t      -> Num t
  Val v      -> Val v
  Op2 op a b -> Op2 op (adjustDepths a depth) (adjustDepths b depth)
  Op1 op a   -> Op1 op (adjustDepths a depth)
  Sig t f    -> Sig (adjustDepths t depth) (adjustDepths f depth)
  Tup a b    -> Tup (adjustDepths a depth) (adjustDepths b depth)
  SigM f     -> SigM (adjustDepths f depth)
  All t f    -> All (adjustDepths t depth) (adjustDepths f depth)
  Lam k t f  -> Lam k (fmap (\t' -> adjustDepths t' depth) t) (\x -> adjustDepths (f (Var k depth)) (depth + 1))
  App f a    -> App (adjustDepths f depth) (adjustDepths a depth)
  Eql t a b  -> Eql (adjustDepths t depth) (adjustDepths a depth) (adjustDepths b depth)
  Rfl        -> Rfl
  EqlM f     -> EqlM (adjustDepths f depth)
  Rwt e f    -> Rwt (adjustDepths e depth) (adjustDepths f depth)
  Met n t ctx -> Met n (adjustDepths t depth) (map (\c -> adjustDepths c depth) ctx)
  Era        -> Era
  Sup l a b  -> Sup (adjustDepths l depth) (adjustDepths a depth) (adjustDepths b depth)
  SupM l f   -> SupM (adjustDepths l depth) (adjustDepths f depth)
  Loc s t    -> Loc s (adjustDepths t depth)
  Log s x    -> Log (adjustDepths s depth) (adjustDepths x depth)
  Pri p      -> Pri p
  Pat ts ms cs -> Pat (map (\t -> adjustDepths t depth) ts) 
                      [(k, adjustDepths v depth) | (k, v) <- ms]
                      [([adjustDepths p depth | p <- ps], adjustDepths t depth) | (ps, t) <- cs]
  Frk l a b  -> Frk (adjustDepths l depth) (adjustDepths a depth) (adjustDepths b depth)

-- Show instances  
-- ==============

instance Show Term where
  show = showTerm False False

instance Show Book where
  show (Book defs names) = unlines [showDefn name (defs M.! name) | name <- names]
    where showDefn k (_, x, t) = k ++ " : " ++ show t ++ " = " ++ showTerm False True x

instance Show Span where
  show span = "\n\x1b[1mLocation:\x1b[0m \x1b[2m(line " ++ show (fst $ spanBeg span) ++ ", column " ++ show (snd $ spanBeg span) ++ ")\x1b[0m\n" ++ highlightError (spanBeg span) (spanEnd span) (spanSrc span)

showHint :: Maybe String -> String
showHint Nothing = ""
showHint (Just h) = "\x1b[1mHint:\x1b[0m " ++ h ++ "\n"

instance Show Error where
  show err = case err of
    CantInfer span ctx hint       -> "\x1b[1mCantInfer:\x1b[0m\n" ++ showHint hint ++ "\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span
    Unsupported span ctx hint     -> "\x1b[1mUnsupported:\x1b[0m\nCurrently, Bend doesn't support matching on non-var expressions.\nThis will be added later. For now, please split this definition.\n" ++ showHint hint ++ "\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span
    Undefined span ctx name hint  -> "\x1b[1mUndefined:\x1b[0m " ++ name ++ "\n" ++ showHint hint ++ "\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span
    TypeMismatch span ctx goal typ hint -> "\x1b[1mMismatch:\x1b[0m\n- Goal: " ++ showTerm False True goal ++ "\n- Type: " ++ showTerm False True typ ++ "\n" ++ showHint hint ++ "\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span
    TermMismatch span ctx a b hint -> "\x1b[1mMismatch:\x1b[0m\n- " ++ showTerm False True a ++ "\n- " ++ showTerm False True b ++ "\n" ++ showHint hint ++ "\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span
    IncompleteMatch span ctx hint -> "\x1b[1mIncompleteMatch:\x1b[0m\n" ++ showHint hint ++ "\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span
    UnknownTermination term  -> "\x1b[1mUnknownTermination:\x1b[0m " ++ show term
    ImportError span msg     -> "\x1b[1mImportError:\x1b[0m " ++ msg ++ show span
    AmbiguousConstructor span ctx ctor fqns hint -> "\x1b[1mAmbiguousConstructor:\x1b[0m &" ++ ctor ++ "\nCould be:\n" ++ unlines ["  - &" ++ fqn | fqn <- fqns] ++ showHint hint ++ "\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span

instance Show Ctx where
  show (Ctx ctx) = case lines of
    [] -> ""
    _  -> init (unlines lines)
    where
      lines = map snd (reverse (clean S.empty (reverse (map showAnn ctx))))
      showAnn (k, _, t) = (k, "- " ++ k ++ " : " ++ show t)
      clean _ [] = []
      clean seen ((n,l):xs)
        | n `S.member` seen = clean seen xs
        | take 1 n == "_"   = clean seen xs
        | otherwise         = (n,l) : clean (S.insert n seen) xs

errorWithSpan :: Span -> String -> a
errorWithSpan span msg = unsafePerformIO $ do
  hPutStrLn stderr msg
  hPutStrLn stderr (show span)
  exitFailure
