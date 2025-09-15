{-./Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Show where

import Core.Type
import Data.List (intercalate, unsnoc, isInfixOf, isPrefixOf)
import Data.List.Split (splitOn)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M
import qualified Data.Set as S
import Highlight (highlightError)

import System.Exit
import System.IO
import System.IO.Unsafe (unsafePerformIO)

-- ============================================================================
-- Display Configuration
-- ============================================================================

-- | Display context containing all parameters needed for term display
data ShowCtx = ShowCtx
  { ctxShadowed  :: S.Set String  -- ^ Variables that are shadowed (need depth annotation)
  , ctxAmbiguous :: S.Set String  -- ^ Names that are ambiguous (need full qualification)
  , ctxDepth     :: Int           -- ^ Current binding depth
  , ctxShowFQN   :: Bool          -- ^ Whether to show fully qualified names
  }

-- | Create default context
defaultCtx :: ShowCtx
defaultCtx = ShowCtx S.empty S.empty 0 False

-- | Increment depth in context
incDepth :: ShowCtx -> ShowCtx
incDepth ctx = ctx { ctxDepth = ctxDepth ctx + 1 }

-- | Update context with new depth
withDepth :: Int -> ShowCtx -> ShowCtx
withDepth d ctx = ctx { ctxDepth = d }

-- ============================================================================
-- Main Entry Points
-- ============================================================================

-- | Main entry point for term display with optional depth tracking and FQN display
showTerm :: Bool -> Bool -> Term -> String
showTerm showFQN trackDepth term = case showFQN of
  True  -> showPlain (defaultCtx { ctxShowFQN = True }) term  -- Show full FQNs
  False -> case trackDepth of
    True  -> showWithShadowing term
    False -> showWithoutPrefixes term

-- | Show terms with depth annotations for shadowed variables only
showWithShadowing :: Term -> String
showWithShadowing term = case S.null shadowed of
  True  -> showPlain defaultCtx term
  False -> showPlain (defaultCtx { ctxShadowed = shadowed }) adjusted
  where
    shadowed = getShadowed term
    adjusted = adjustDepths term 0

-- | Show terms without module prefixes (unless ambiguous)
showWithoutPrefixes :: Term -> String
showWithoutPrefixes term = showPlain (defaultCtx { ctxAmbiguous = ambiguous }) term
  where
    ambiguous = getAmbiguousNames term

-- ============================================================================
-- Core Term Display
-- ============================================================================

showPlain :: ShowCtx -> Term -> String
showPlain ctx term = case term of
  -- Variables and references
  Var k i      -> showVar (ctxShadowed ctx) k i
  Ref k i      -> showName ctx k
  Sub t        -> showPlain ctx t

  -- Binding forms
  Fix k f      -> showFix ctx k f
  Let k t v f  -> showLet ctx k t v f
  Use k v f    -> showUse ctx k v f

  -- Types and annotations
  Set          -> "Set"
  Chk x t      -> "(" ++ showPlain ctx x ++ "::" ++ showPlain ctx t ++ ")"
  Tst x        -> "trust " ++ showPlain ctx x

  -- Empty
  Emp          -> "Empty"
  EmpM         -> "λ{}"

  -- Unit
  Uni          -> "Unit"
  One          -> "()"
  UniM f       -> "λ{():" ++ showPlain ctx f ++ "}"

  -- Bool
  Bit          -> "Bool"
  Bt0          -> "False"
  Bt1          -> "True"
  BitM f t     -> "λ{False:" ++ showPlain ctx f ++ ";True:" ++ showPlain ctx t ++ "}"

  -- Nat
  Nat          -> "Nat"
  Zer          -> "0n"
  Suc _        -> showSuc ctx term
  NatM z s     -> "λ{0n:" ++ showPlain ctx z ++ ";1n+:" ++ showPlain ctx s ++ "}"

  -- List
  Lst t        -> showPlain ctx t ++ "[]"
  Nil          -> "[]"
  Con h t      -> showCon ctx h t
  LstM n c     -> "λ{[]:" ++ showPlain ctx n ++ ";<>:" ++ showPlain ctx c ++ "}"

  -- Enum
  Enu s        -> "enum{" ++ intercalate "," (map ("&" ++) s) ++ "}"
  Sym s        -> "&" ++ showName ctx s
  EnuM cs d    -> showEnuM ctx cs d

  -- Pair
  Sig a b      -> showSig ctx a b
  Tup _ _      -> showTup ctx term
  SigM f       -> "λ{(,):" ++ showPlain ctx f ++ "}"

  -- Function
  All a b      -> showAll ctx a b
  Lam k t f    -> showLam ctx k t f
  App _ _      -> showApp ctx term

  -- Equality
  Eql t a b    -> showEql ctx t a b
  Rfl          -> "{==}"
  EqlM f       -> "λ{{==}:" ++ showPlain ctx f ++ "}"
  Rwt e f      -> "rewrite " ++ showPlain ctx e ++ " " ++ showPlain ctx f

  -- Meta and superposition
  Met n t ctxs -> "?" ++ n ++ ":" ++ showPlain ctx t ++ "{" ++ intercalate "," (map (showPlain ctx) ctxs) ++ "}"
  Era          -> "*"
  Sup l a b    -> "&" ++ showPlain ctx l ++ "{" ++ showPlain ctx a ++ "," ++ showPlain ctx b ++ "}"
  SupM l f     -> "λ{&" ++ showPlain ctx l ++ "{,}:" ++ showPlain ctx f ++ "}"

  -- Location and logging
  Loc _ t      -> showPlain ctx t
  Log s x      -> "log " ++ showPlain ctx s ++ " " ++ showPlain ctx x

  -- Primitives
  Pri p        -> showPri p
  Num t        -> showNum t
  Val v        -> showVal v
  Op2 o a b    -> showOp2 ctx o a b
  Op1 o a      -> showOp1 ctx o a

  -- Patterns
  Pat ts ms cs -> showPat ctx ts ms cs
  Frk l a b    -> "fork " ++ showPlain ctx l ++ ":" ++ showPlain ctx a ++ " else:" ++ showPlain ctx b

-- | Show a name, respecting FQN and ambiguity settings
showName :: ShowCtx -> String -> String
showName ctx name
  | ctxShowFQN ctx = name
  | otherwise      = stripPrefix (ctxAmbiguous ctx) name

-- ============================================================================
-- Binding Display Functions
-- ============================================================================

-- | Show variable with depth annotation if shadowed: x or x^2
showVar :: S.Set String -> String -> Int -> String
showVar shadowed k i = case S.member k shadowed of
  True  -> k ++ "^" ++ show i
  False -> k

-- | μx. body
showFix :: ShowCtx -> String -> Body -> String
showFix ctx k f = "μ" ++ kStr ++ ". " ++ showPlain (incDepth ctx) (f (Var k (ctxDepth ctx)))
  where kStr = varName (ctxShadowed ctx) k (ctxDepth ctx)

-- | x : T = v body or x = v body
showLet :: ShowCtx -> String -> Maybe Term -> Term -> Body -> String
showLet ctx k t v f = case t of
  Just t  -> kStr ++ " : " ++ showPlain ctx t ++ " = " ++ showPlain ctx v ++ " " ++ showPlain (incDepth ctx) (f (Var k (ctxDepth ctx)))
  Nothing -> kStr ++ " = " ++ showPlain ctx v ++ " " ++ showPlain (incDepth ctx) (f (Var k (ctxDepth ctx)))
  where kStr = varName (ctxShadowed ctx) k (ctxDepth ctx)

-- | use x = v body
showUse :: ShowCtx -> String -> Term -> Body -> String
showUse ctx k v f = "use " ++ varName (ctxShadowed ctx) k (ctxDepth ctx) ++ " = " ++ showPlain ctx v ++ " " ++ showPlain (incDepth ctx) (f (Var k (ctxDepth ctx)))

-- | Lambda abstraction: λx:T. body or λx. body
showLam :: ShowCtx -> String -> Maybe Term -> Body -> String
showLam ctx k t f = case t of
  Just t  -> "λ" ++ varName (ctxShadowed ctx) k (ctxDepth ctx) ++ ":" ++ showPlain ctx t ++ ". " ++ showPlain (incDepth ctx) (f (Var k (ctxDepth ctx)))
  Nothing -> "λ" ++ varName (ctxShadowed ctx) k (ctxDepth ctx) ++ ". " ++ showPlain (incDepth ctx) (f (Var k (ctxDepth ctx)))

-- ============================================================================
-- Data Structure Display
-- ============================================================================

-- | Count successor applications: 3n or 2n+x
showSuc :: ShowCtx -> Term -> String
showSuc ctx term = case count term of
  (k, Zer) -> show (k :: Integer) ++ "n"
  (k, r)   -> show (k :: Integer) ++ "n+" ++ showPlain ctx r
  where
    count (cut -> Suc t) = let (c, r) = count t in (c + 1, r)
    count t              = (0 :: Integer, t)

-- | List constructor: h<>t or "string" for character lists
showCon :: ShowCtx -> Term -> Term -> String
showCon ctx h t = fromMaybe plain (showStr ctx (Con h t))
  where plain = showPlain ctx h ++ "<>" ++ showPlain ctx t

-- | Tuple: (a,b,c) or @Ctor{a,b}
showTup :: ShowCtx -> Term -> String
showTup ctx term = fromMaybe plain (showCtr ctx term)
  where plain = "(" ++ intercalate "," (map (showPlain ctx) (flattenTup term)) ++ ")"

-- | Function application: f(x,y,z)
showApp :: ShowCtx -> Term -> String
showApp ctx term = fnStr ++ "(" ++ intercalate "," (map (showPlain ctx) args) ++ ")"
  where
    (fn, args) = collectApps term []
    fnStr = case cut fn of
      Var k i -> showVar (ctxShadowed ctx) k i
      Ref k i -> showName ctx k
      _       -> "(" ++ showPlain ctx fn ++ ")"

-- | Enum matcher: λ{&foo:x;&bar:y;default}
showEnuM :: ShowCtx -> [(String,Term)] -> Term -> String
showEnuM ctx cs d = "λ{" ++ intercalate ";" cases ++ ";" ++ showPlain ctx d ++ "}"
  where cases = map (\(s,t) -> "&" ++ showName ctx s ++ ":" ++ showPlain ctx t) cs

-- ============================================================================
-- Type Display Functions
-- ============================================================================

-- | Dependent pair type: Σx:A. B or A & B
showSig :: ShowCtx -> Term -> Term -> String
showSig ctx a b = case cut b of
  Lam "_" t f -> "(" ++ showArg a ++ " & " ++ showCodomain (f (Var "_" (ctxDepth ctx))) ++ ")"
  Lam k t f   -> "Σ" ++ varName (ctxShadowed ctx) k (ctxDepth ctx) ++ ":" ++ showArg a ++ ". " ++ showPlain (incDepth ctx) (f (Var k (ctxDepth ctx)))
  _           -> "Σ" ++ showArg a ++ ". " ++ showPlain ctx b
  where
    showArg t = case cut t of
      All{} -> "(" ++ showPlain ctx t ++ ")"
      Sig{} -> "(" ++ showPlain ctx t ++ ")"
      _     -> showPlain ctx t
    showCodomain t = case t of
      Sig _ (Lam k _ _) | k /= "_" -> "(" ++ showPlain (incDepth ctx) t ++ ")"
      _                           -> showPlain (incDepth ctx) t

-- | Dependent function type: ∀x:A. B or A -> B
showAll :: ShowCtx -> Term -> Term -> String
showAll ctx a b = case b of
  Lam "_" t f -> showArg a ++ " -> " ++ showCodomain (f (Var "_" (ctxDepth ctx)))
  Lam k t f   -> "∀" ++ varName (ctxShadowed ctx) k (ctxDepth ctx) ++ ":" ++ showArg a ++ ". " ++ showPlain (incDepth ctx) (f (Var k (ctxDepth ctx)))
  _           -> "∀" ++ showArg a ++ ". " ++ showPlain ctx b
  where
    showArg t = case cut t of
      All{} -> "(" ++ showPlain ctx t ++ ")"
      Sig{} -> "(" ++ showPlain ctx t ++ ")"
      _     -> showPlain ctx t
    showCodomain t = case t of
      All _ (Lam k _ _) | k /= "_" -> "(" ++ showPlain (incDepth ctx) t ++ ")"
      _                           -> showPlain (incDepth ctx) t

-- | Equality type: T{a == b}
showEql :: ShowCtx -> Term -> Term -> Term -> String
showEql ctx t a b = typeStr ++ "{" ++ showPlain ctx a ++ "==" ++ showPlain ctx b ++ "}"
  where
    typeStr = case t of
      Sig _ _ -> "(" ++ showPlain ctx t ++ ")"
      All _ _ -> "(" ++ showPlain ctx t ++ ")"
      _      -> showPlain ctx t

-- ============================================================================
-- Operator and Pattern Display
-- ============================================================================

-- | Binary operator: (a + b)
showOp2 :: ShowCtx -> NOp2 -> Term -> Term -> String
showOp2 ctx op a b = "(" ++ showPlain ctx a ++ " " ++ opStr ++ " " ++ showPlain ctx b ++ ")"
  where
    opStr = case op of
      ADD -> "+";   SUB -> "-";   MUL -> "*";   DIV -> "/"
      MOD -> "%";   POW -> "**";  EQL -> "==";  NEQ -> "!=="
      LST -> "<";   GRT -> ">";   LEQ -> "<=";  GEQ -> ">="
      AND -> "&&";  OR  -> "|";   XOR -> "^"
      SHL -> "<<";  SHR -> ">>"

-- | Unary operator: (not a) or (-a)
showOp1 :: ShowCtx -> NOp1 -> Term -> String
showOp1 ctx op a = case op of
  NOT -> "(not " ++ showPlain ctx a ++ ")"
  NEG -> "(-" ++ showPlain ctx a ++ ")"

-- | Pattern match: match x { with k=v case (p): body }
showPat :: ShowCtx -> [Term] -> [Move] -> [Case] -> String
showPat ctx ts ms cs = "match " ++ unwords (map (showPlain ctx) ts) ++ " {" ++ moves ++ cases ++ " }"
  where
    moves = case ms of
      [] -> ""
      _  -> " with " ++ intercalate " with " (map showMove ms)
    cases = case cs of
      [] -> ""
      _  -> " " ++ intercalate " " (map showCase cs)
    showMove (k,x) = k ++ "=" ++ showPlain ctx x
    showCase (ps,x) = "case " ++ unwords (map showPat' ps) ++ ": " ++ showPlain ctx x
    showPat' p = "(" ++ showPlain ctx p ++ ")"

-- ============================================================================
-- Primitive Display
-- ============================================================================

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

-- ============================================================================
-- Formatting Utilities
-- ============================================================================

-- | Try to display character list as string literal: "hello"
showStr :: ShowCtx -> Term -> Maybe String
showStr ctx term = go [] term
  where
    go acc Nil                        = Just ("\"" ++ reverse acc ++ "\"")
    go acc (Con (Val (CHR_V c)) rest) = go (c:acc) rest
    go acc (Loc _ t)                  = go acc t
    go _   _                          = Nothing

-- | Try to display tuple as constructor: @Ctor{a,b}
showCtr :: ShowCtx -> Term -> Maybe String
showCtr ctx t =
  let ts = map cut (flattenTup t) in
  case unsnoc ts of
    Just ((Sym name : ts), One) -> Just ("@" ++ showName ctx name ++ "{" ++ intercalate "," (map show ts) ++ "}")
    _                           -> Nothing

-- ============================================================================
-- Name Resolution Utilities
-- ============================================================================

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

-- ============================================================================
-- Depth Tracking for Shadowing
-- ============================================================================

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

-- ============================================================================
-- Show Instances
-- ============================================================================

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
    AmbiguousEnum span ctx ctor fqns hint -> "\x1b[1mAmbiguousEnum:\x1b[0m &" ++ ctor ++ "\nCould be:\n" ++ unlines ["  - &" ++ fqn | fqn <- fqns] ++ showHint hint ++ "\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span

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
