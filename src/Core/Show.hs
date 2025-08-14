{-./Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Show where

import Core.Type
import Data.List (intercalate)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M
import qualified Data.Set as S
import Highlight (highlightError)

import System.Exit
import System.IO
import System.IO.Unsafe (unsafePerformIO)

-- Term Display
-- ============

-- | Main entry point for term display with optional depth tracking
showTerm :: Bool -> Term -> String
showTerm trackDepth term = case trackDepth of
  True  -> showWithShadowing term
  False -> showPlain S.empty term 0

-- | Show terms with depth annotations for shadowed variables only
showWithShadowing :: Term -> String
showWithShadowing term = case S.null shadowed of
  True  -> showPlain S.empty term 0  
  False -> showPlain shadowed adjusted 0
  where
    shadowed = getShadowed term
    adjusted = adjustDepths term 0

showPlain :: S.Set String -> Term -> Int -> String
showPlain shadowed term depth = case term of
  -- Variables
  Var k i      -> showVar shadowed k i
  Ref k i      -> k
  Sub t        -> showPlain shadowed t depth

  -- Binding forms
  Fix k f      -> showFix shadowed k f depth
  Let k t v f  -> showLet shadowed k t v f depth
  Use k v f    -> showUse shadowed k v f depth

  -- Types and annotations
  Set          -> "Set"
  Chk x t      -> "(" ++ showPlain shadowed x depth ++ "::" ++ showPlain shadowed t depth ++ ")"

  -- Empty
  Emp          -> "Empty"
  EmpM         -> "λ{}"

  -- Unit
  Uni          -> "Unit"
  One          -> "()"
  UniM f       -> "λ{():" ++ showPlain shadowed f depth ++ "}"

  -- Bool
  Bit          -> "Bool"
  Bt0          -> "False"
  Bt1          -> "True"
  BitM f t     -> "λ{False:" ++ showPlain shadowed f depth ++ ";True:" ++ showPlain shadowed t depth ++ "}"

  -- Nat
  Nat          -> "Nat"
  Zer          -> "0n"
  Suc _        -> showSuc shadowed term depth
  NatM z s     -> "λ{0n:" ++ showPlain shadowed z depth ++ ";1n+:" ++ showPlain shadowed s depth ++ "}"

  -- List
  Lst t        -> showPlain shadowed t depth ++ "[]"
  Nil          -> "[]"
  Con h t      -> showCon shadowed h t depth
  LstM n c     -> "λ{[]:" ++ showPlain shadowed n depth ++ ";<>:" ++ showPlain shadowed c depth ++ "}"

  -- Enum
  Enu s        -> "enum{" ++ intercalate "," (map ("&" ++) s) ++ "}"
  Sym s        -> "&" ++ s
  EnuM cs d    -> showEnuM shadowed cs d depth

  -- Pair
  Sig a b      -> showSig shadowed a b depth
  Tup _ _      -> showTup shadowed term depth  
  SigM f       -> "λ{(,):" ++ showPlain shadowed f depth ++ "}"

  -- Function
  All a b      -> showAll shadowed a b depth
  Lam k t f    -> showLam shadowed k t f depth
  App _ _      -> showApp shadowed term depth

  -- Equality
  Eql t a b    -> showEql shadowed t a b depth
  Rfl          -> "{==}"
  EqlM f       -> "λ{{==}:" ++ showPlain shadowed f depth ++ "}"
  Rwt e f      -> "rewrite " ++ showPlain shadowed e depth ++ " " ++ showPlain shadowed f depth

  -- Meta and superposition
  Met n t ctx  -> "?" ++ n ++ ":" ++ showPlain shadowed t depth ++ "{" ++ intercalate "," (map (\c -> showPlain shadowed c depth) ctx) ++ "}"
  Era          -> "*"
  Sup l a b    -> "&" ++ showPlain shadowed l depth ++ "{" ++ showPlain shadowed a depth ++ "," ++ showPlain shadowed b depth ++ "}"
  SupM l f     -> "λ{&" ++ showPlain shadowed l depth ++ "{,}:" ++ showPlain shadowed f depth ++ "}"

  -- Location and logging
  Loc _ t      -> showPlain shadowed t depth
  Log s x      -> "log " ++ showPlain shadowed s depth ++ " " ++ showPlain shadowed x depth

  -- Primitives
  Pri p        -> showPri p
  Num t        -> showNum t
  Val v        -> showVal v
  Op2 o a b    -> showOp2 shadowed o a b depth
  Op1 o a      -> showOp1 shadowed o a depth

  -- Patterns
  Pat ts ms cs -> showPat shadowed ts ms cs depth
  Frk l a b    -> "fork " ++ showPlain shadowed l depth ++ ":" ++ showPlain shadowed a depth ++ " else:" ++ showPlain shadowed b depth

-- Helper functions for complex cases
-- ==================================

-- | Show variable with depth annotation if shadowed: x or x^2
showVar :: S.Set String -> String -> Int -> String
showVar shadowed k i = case S.member k shadowed of
  True  -> k ++ "^" ++ show i
  False -> k

-- | μx. body
showFix :: S.Set String -> String -> Body -> Int -> String
showFix shadowed k f depth = "μ" ++ kStr ++ ". " ++ showPlain shadowed (f (Var k depth)) (depth + 1)
  where kStr = varName shadowed k depth

-- | x : T = v body or x = v body
showLet :: S.Set String -> String -> Maybe Term -> Term -> Body -> Int -> String
showLet shadowed k t v f depth = case t of
  Just t  -> kStr ++ " : " ++ showPlain shadowed t depth ++ " = " ++ showPlain shadowed v depth ++ " " ++ showPlain shadowed (f (Var k depth)) (depth + 1)
  Nothing -> kStr ++ " = " ++ showPlain shadowed v depth ++ " " ++ showPlain shadowed (f (Var k depth)) (depth + 1)
  where kStr = varName shadowed k depth

-- | use x = v body
showUse :: S.Set String -> String -> Term -> Body -> Int -> String
showUse shadowed k v f depth = "use " ++ varName shadowed k depth ++ " = " ++ showPlain shadowed v depth ++ " " ++ showPlain shadowed (f (Var k depth)) (depth + 1)

-- | Count successor applications: 3n or 2n+x
showSuc :: S.Set String -> Term -> Int -> String
showSuc shadowed term depth = case count term of
  (k, Zer) -> show (k :: Integer) ++ "n"
  (k, r)   -> show (k :: Integer) ++ "n+" ++ showPlain shadowed r depth
  where
    count (cut -> Suc t) = let (c, r) = count t in (c + 1, r)
    count t              = (0 :: Integer, t)

-- | List constructor: h<>t or "string" for character lists
showCon :: S.Set String -> Term -> Term -> Int -> String
showCon shadowed h t depth = fromMaybe plain (showStr shadowed (Con h t) depth)
  where plain = showPlain shadowed h depth ++ "<>" ++ showPlain shadowed t depth

-- | Enum matcher: λ{&foo:x;&bar:y;default}
showEnuM :: S.Set String -> [(String,Term)] -> Term -> Int -> String
showEnuM shadowed cs d depth = "λ{" ++ intercalate ";" cases ++ ";" ++ showPlain shadowed d depth ++ "}"
  where cases = map (\(s,t) -> "&" ++ s ++ ":" ++ showPlain shadowed t depth) cs

-- | Dependent pair type: Σx:A. B or A & B
showSig :: S.Set String -> Term -> Term -> Int -> String
showSig shadowed a b depth = case cut b of
  Lam "_" t f -> "(" ++ showArg a ++ " & " ++ showCodomain (f (Var "_" depth)) ++ ")"
  Lam k t f   -> "Σ" ++ varName shadowed k depth ++ ":" ++ showArg a ++ ". " ++ showPlain shadowed (f (Var k depth)) (depth + 1)
  _           -> "Σ" ++ showArg a ++ ". " ++ showPlain shadowed b depth
  where
    showArg t = case cut t of
      All{} -> "(" ++ showPlain shadowed t depth ++ ")"
      Sig{} -> "(" ++ showPlain shadowed t depth ++ ")"
      _     -> showPlain shadowed t depth
    showCodomain t = case t of
      Sig _ (Lam k _ _) | k /= "_" -> "(" ++ showPlain shadowed t (depth + 1) ++ ")"
      _                           -> showPlain shadowed t (depth + 1)

-- | Dependent function type: ∀x:A. B or A -> B
showAll :: S.Set String -> Term -> Term -> Int -> String
showAll shadowed a b depth = case b of
  Lam "_" t f -> showArg a ++ " -> " ++ showCodomain (f (Var "_" depth))
  Lam k t f   -> "∀" ++ varName shadowed k depth ++ ":" ++ showArg a ++ ". " ++ showPlain shadowed (f (Var k depth)) (depth + 1)
  _           -> "∀" ++ showArg a ++ ". " ++ showPlain shadowed b depth
  where
    showArg t = case cut t of
      All{} -> "(" ++ showPlain shadowed t depth ++ ")"
      Sig{} -> "(" ++ showPlain shadowed t depth ++ ")"
      _     -> showPlain shadowed t depth
    showCodomain t = case t of
      All _ (Lam k _ _) | k /= "_" -> "(" ++ showPlain shadowed t (depth + 1) ++ ")"
      _                           -> showPlain shadowed t (depth + 1)

-- | Lambda abstraction: λx:T. body or λx. body
showLam :: S.Set String -> String -> Maybe Term -> Body -> Int -> String
showLam shadowed k t f depth = case t of
  Just t  -> "λ" ++ varName shadowed k depth ++ ":" ++ showPlain shadowed t depth ++ ". " ++ showPlain shadowed (f (Var k depth)) (depth + 1)
  Nothing -> "λ" ++ varName shadowed k depth ++ ". " ++ showPlain shadowed (f (Var k depth)) (depth + 1)

-- | Function application: f(x,y,z)
showApp :: S.Set String -> Term -> Int -> String
showApp shadowed term depth = fnStr ++ "(" ++ intercalate "," (map (\arg -> showPlain shadowed arg depth) args) ++ ")"
  where 
    (fn, args) = collectApps term []
    fnStr = case cut fn of
      Var k i -> showVar shadowed k i
      Ref k i -> k  
      _       -> "(" ++ showPlain shadowed fn depth ++ ")"

-- | Tuple: (a,b,c) or @Ctor{a,b}
showTup :: S.Set String -> Term -> Int -> String
showTup shadowed term depth = fromMaybe plain (showCtr term)
  where plain = "(" ++ intercalate "," (map (\t -> showPlain shadowed t depth) (flattenTup term)) ++ ")"

-- | Equality type: T{a == b}
showEql :: S.Set String -> Term -> Term -> Term -> Int -> String  
showEql shadowed t a b depth = typeStr ++ "{" ++ showPlain shadowed a depth ++ "==" ++ showPlain shadowed b depth ++ "}"
  where 
    typeStr = case t of
      Sig _ _ -> "(" ++ showPlain shadowed t depth ++ ")"
      All _ _ -> "(" ++ showPlain shadowed t depth ++ ")"
      _      -> showPlain shadowed t depth

-- | Binary operator: (a + b)
showOp2 :: S.Set String -> NOp2 -> Term -> Term -> Int -> String
showOp2 shadowed op a b depth = "(" ++ showPlain shadowed a depth ++ " " ++ opStr ++ " " ++ showPlain shadowed b depth ++ ")"
  where
    opStr = case op of
      ADD -> "+";   SUB -> "-";   MUL -> "*";   DIV -> "/"
      MOD -> "%";   POW -> "**";  EQL -> "==";  NEQ -> "!==" 
      LST -> "<";   GRT -> ">";   LEQ -> "<=";  GEQ -> ">="
      AND -> "&&";  OR  -> "|";   XOR -> "^"
      SHL -> "<<";  SHR -> ">>"

-- | Unary operator: (not a) or (-a)
showOp1 :: S.Set String -> NOp1 -> Term -> Int -> String
showOp1 shadowed op a depth = case op of
  NOT -> "(not " ++ showPlain shadowed a depth ++ ")"
  NEG -> "(-" ++ showPlain shadowed a depth ++ ")"

-- | Pattern match: match x { with k=v case (p): body }
showPat :: S.Set String -> [Term] -> [Move] -> [Case] -> Int -> String
showPat shadowed ts ms cs depth = "match " ++ unwords (map (\t -> showPlain shadowed t depth) ts) ++ " {" ++ moves ++ cases ++ " }"
  where
    moves = case ms of
      [] -> ""
      _  -> " with " ++ intercalate " with " (map showMove ms)
    cases = case cs of  
      [] -> ""
      _  -> " " ++ intercalate " " (map showCase cs)
    showMove (k,x) = k ++ "=" ++ showPlain shadowed x depth
    showCase (ps,x) = "case " ++ unwords (map showPat' ps) ++ ": " ++ showPlain shadowed x depth
    showPat' p = "(" ++ showPlain shadowed p depth ++ ")"

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
showStr :: S.Set String -> Term -> Int -> Maybe String  
showStr shadowed term depth = go [] term
  where
    go acc Nil                        = Just ("\"" ++ reverse acc ++ "\"")
    go acc (Con (Val (CHR_V c)) rest) = go (c:acc) rest
    go acc (Loc _ t)                  = go acc t
    go _   _                          = Nothing

-- | Try to display tuple as constructor: @Ctor{a,b}
showCtr :: Term -> Maybe String
showCtr (Tup (Sym name) rest) = case lastElem rest of
  Just One -> Just ("@" ++ name ++ "{" ++ intercalate "," (map show (init (flattenTup rest))) ++ "}")
  _        -> Nothing
  where
    lastElem (Tup _ r) = lastElem r
    lastElem t         = Just t
showCtr _ = Nothing

-- Utility functions
-- =================

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
  show = showTerm False

instance Show Book where
  show (Book defs names) = unlines [showDefn name (defs M.! name) | name <- names]
    where showDefn k (_, x, t) = k ++ " : " ++ show t ++ " = " ++ showTerm True x

instance Show Span where
  show span = "\n\x1b[1mLocation:\x1b[0m \x1b[2m(line " ++ show (fst $ spanBeg span) ++ ", column " ++ show (snd $ spanBeg span) ++ ")\x1b[0m\n" ++ highlightError (spanBeg span) (spanEnd span) (spanSrc span)

instance Show Error where
  show err = case err of
    CantInfer span ctx       -> "\x1b[1mCantInfer:\x1b[0m\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span
    Unsupported span ctx     -> "\x1b[1mUnsupported:\x1b[0m\nCurrently, Bend doesn't support matching on non-var expressions.\nThis will be added later. For now, please split this definition.\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span
    Undefined span ctx name  -> "\x1b[1mUndefined:\x1b[0m " ++ name ++ "\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span
    TypeMismatch span ctx goal typ -> "\x1b[1mMismatch:\x1b[0m\n- Goal: " ++ showTerm True goal ++ "\n- Type: " ++ showTerm True typ ++ "\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span
    TermMismatch span ctx a b -> "\x1b[1mMismatch:\x1b[0m\n- " ++ showTerm True a ++ "\n- " ++ showTerm True b ++ "\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span
    IncompleteMatch span ctx -> "\x1b[1mIncompleteMatch:\x1b[0m\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span
    UnknownTermination term  -> "\x1b[1mUnknownTermination:\x1b[0m " ++ show term
    ImportError span msg     -> "\x1b[1mImportError:\x1b[0m " ++ msg ++ show span

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
