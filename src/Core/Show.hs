{-./Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Show where

import Core.Type
import Data.List (intercalate)
import Data.Maybe (fromMaybe, fromJust)
import qualified Data.Map as M
import qualified Data.Set as S
import Highlight (highlightError)

import System.Exit
import System.IO
import System.IO.Unsafe (unsafePerformIO)
import Debug.Trace

-- | Basic Term show instance without depth annotations
instance Show Term where
  show (Var k i)      = k -- ++ "^" ++ show i
  show (Ref k i)      = k -- ++ "!"
  show (Sub t)        = show t
  show (Fix k f)      = "μ" ++ k ++ ". " ++ show (f (Var k 0))
  show (Let k t v f)  = case t of
    Just t  -> k ++ " : " ++ show t ++ " = " ++ show v ++ " " ++ show (f (Var k 0))
    Nothing -> k ++                    " = " ++ show v ++ " " ++ show (f (Var k 0))
  show (Use k v f)    = "use " ++ k ++ " = " ++ show v ++ " " ++ show (f (Var k 0))
  show (Set)          = "Set"
  show (Chk x t)      = "(" ++ show x ++ "::" ++ show t ++ ")"
  show (Emp)          = "Empty"
  show (EmpM)         = "λ{}"
  show (Uni)          = "Unit"
  show (One)          = "()"
  show (UniM f)       = "λ{():" ++ show f ++ "}"
  show (Bit)          = "Bool"
  show (Bt0)          = "False"
  show (Bt1)          = "True"
  show (BitM f t)     = "λ{False:" ++ show f ++ ";True:" ++ show t ++ "}"
  show (Nat)          = "Nat"
  show (Zer)          = "0n"
  show term@(Suc _) =
    let (k, rest) = count term in
    case cut rest of
      Zer -> show k ++ "n"
      _   -> show k ++ "n+" ++ show rest
    where count :: Term -> (Int, Term)
          count (cut -> Suc t) = let (c, r) = count t in (c + 1, r)
          count t              = (0, t)
  show (NatM z s)     = "λ{0n:" ++ show z ++ ";1n+:" ++ show s ++ "}"
  show (Lst t)        = show t ++ "[]"
  show (Nil)          = "[]"
  show (Con h t)      = fromMaybe (show h ++ "<>" ++ show t) (Core.Show.prettyStr (Con h t))
  show (LstM n c)     = "λ{[]:" ++ show n ++ ";<>:" ++ show c ++ "}"
  show (Enu s)        = "enum{" ++ intercalate "," (map (\x -> "&" ++ x) s) ++ "}"
  show (Sym s)        = "&" ++ s
  show (EnuM c e)     = "λ{" ++ intercalate ";" (map (\(s,t) -> "&" ++ s ++ ":" ++ show t) c) ++ ";" ++ show e ++ "}"
  show (Sig a b) = case cut b of
      Lam "_" t f -> showArg a ++ " & " ++ showCodomain (f (Var "_" 0))
      Lam k t f   -> "Σ" ++ k ++ ":" ++ showArg a ++ ". " ++ show (f (Var k 0))
      _           -> "Σ" ++ showArg a ++ ". " ++ show b
    where
      showArg t = case cut t of
          All{} -> "(" ++ show t ++ ")"
          Sig{} -> "(" ++ show t ++ ")"
          _     -> show t
      showCodomain t = case t of
          Sig _ (Lam k _ _) | k /= "_" -> "(" ++ show t ++ ")"
          _                           -> show t
  show tup@(Tup _ _)  = fromMaybe ("(" ++ intercalate "," (map show (flattenTup tup)) ++ ")") (prettyCtr tup)
  show (SigM f)       = "λ{(,):" ++ show f ++ "}"
  show (All a b) = case b of
      Lam "_" t f -> showArg a ++ " -> " ++ showCodomain (f (Var "_" 0))
      Lam k t f   -> "∀" ++ k ++ ":" ++ showArg a ++ ". " ++ show (f (Var k 0))
      _           -> "∀" ++ showArg a ++ ". " ++ show b
    where
      showArg t = case cut t of
          All{} -> "(" ++ show t ++ ")"
          Sig{} -> "(" ++ show t ++ ")"
          _     -> show t
      showCodomain t = case t of
          All _ (Lam k _ _) | k /= "_"  -> "(" ++ show t ++ ")"
          _                           -> show t
  show (Lam k t f)      = case t of
    Just t  -> "λ" ++ k ++ ":" ++ show t ++ ". " ++ show (f (Var k 0))
    Nothing -> "λ" ++ k ++ ". " ++ show (f (Var k 0))
  show app@(App _ _)  = fnStr ++ "(" ++ intercalate "," (map show args) ++ ")" where
           (fn, args) = collectApps app []
           fnStr      = case cut fn of
              Var k i -> show (Var k i)
              Ref k i -> show (Ref k i)
              fn      -> "(" ++ show fn ++ ")"
  show (Eql t a b)     = case t of
    (Sig _ _) -> "(" ++ show t ++ ")" ++ "{" ++ show a ++ "==" ++ show b ++ "}"
    (All _ _) -> "(" ++ show t ++ ")" ++ "{" ++ show a ++ "==" ++ show b ++ "}"
    _         ->        show t ++        "{" ++ show a ++ "==" ++ show b ++ "}"
  show (Rfl)           = "{==}"
  show (EqlM f)        = "λ{{==}:" ++ show f ++ "}"
  show (Rwt e f)       = "rewrite " ++ show e ++ " " ++ show f
  show (Loc _ t)       = show t
  show (Era)           = "*"
  show (Sup l a b)     = "&" ++ show l ++ "{" ++ show a ++ "," ++ show b ++ "}"
  show (SupM l f)      = "λ{&" ++ show l ++ "{,}:" ++ show f ++ "}"
  show (Frk l a b)     = "fork " ++ show l ++ ":" ++ show a ++ " else:" ++ show b
  show (Met n t ctx)   = "?" ++ n ++ ":" ++ show t ++ "{" ++ intercalate "," (map show ctx) ++ "}"
  show (Log s x)       = "log " ++ show s ++ " " ++ show x
  show (Pri p)         = pri p where
    pri U64_TO_CHAR    = "U64_TO_CHAR"
    pri CHAR_TO_U64    = "CHAR_TO_U64"
    pri HVM_INC        = "HVM_INC"
    pri HVM_DEC        = "HVM_DEC"
  show (Num U64_T)     = "U64"
  show (Num I64_T)     = "I64"
  show (Num F64_T)     = "F64"
  show (Num CHR_T)     = "Char"
  show (Val (U64_V n)) = show n
  show (Val (I64_V n)) = if n >= 0 then "+" ++ show n else show n
  show (Val (F64_V n)) = show n
  show (Val (CHR_V c)) = "'" ++ showChar c ++ "'" where
         showChar '\n' = "\\n"
         showChar '\t' = "\\t"
         showChar '\r' = "\\r"
         showChar '\0' = "\\0"
         showChar '\\' = "\\\\"
         showChar '\'' = "\\'"
         showChar c    = [c]
  show (Op2 ADD a b)   = "(" ++ show a ++ " + " ++ show b ++ ")"
  show (Op2 SUB a b)   = "(" ++ show a ++ " - " ++ show b ++ ")"
  show (Op2 MUL a b)   = "(" ++ show a ++ " * " ++ show b ++ ")"
  show (Op2 DIV a b)   = "(" ++ show a ++ " / " ++ show b ++ ")"
  show (Op2 MOD a b)   = "(" ++ show a ++ " % " ++ show b ++ ")"
  show (Op2 EQL a b)   = "(" ++ show a ++ " == " ++ show b ++ ")"
  show (Op2 NEQ a b)   = "(" ++ show a ++ " !== " ++ show b ++ ")"
  show (Op2 LST a b)   = "(" ++ show a ++ " < " ++ show b ++ ")"
  show (Op2 GRT a b)   = "(" ++ show a ++ " > " ++ show b ++ ")"
  show (Op2 LEQ a b)   = "(" ++ show a ++ " <= " ++ show b ++ ")"
  show (Op2 GEQ a b)   = "(" ++ show a ++ " >= " ++ show b ++ ")"
  show (Op2 AND a b)   = "(" ++ show a ++ " && " ++ show b ++ ")"
  show (Op2 OR a b)    = "(" ++ show a ++ " | " ++ show b ++ ")"
  show (Op2 XOR a b)   = "(" ++ show a ++ " ^ " ++ show b ++ ")"
  show (Op2 SHL a b)   = "(" ++ show a ++ " << " ++ show b ++ ")"
  show (Op2 SHR a b)   = "(" ++ show a ++ " >> " ++ show b ++ ")"
  show (Op2 POW a b)   = "(" ++ show a ++ " ** " ++ show b ++ ")"
  show (Op1 NOT a)     = "(not " ++ show a ++ ")"
  show (Op1 NEG a)     = "(-" ++ show a ++ ")"
  show (Pat t m c)     = "match " ++ unwords (map show t) ++ " {" ++ showMoves ++ showCases ++ " }" where
             showMoves = if null m then "" else " with " ++ intercalate " with " (map mv m) where
               mv(k,x) = k ++ "=" ++ show x
             showCases = if null c then "" else " " ++ intercalate " " (map cs c) where
               cs(p,x) = "case " ++ unwords (map showPat p) ++ ": " ++ show x
             showPat p = "(" ++ show p ++ ")"

-- | Book show instance with depth annotations for better readability
instance Show Book where
  show (Book defs names) = unlines (map defn [(name, fromJust (M.lookup name defs)) | name <- names])
    where defn (k,(_,x,t)) = k ++ " : " ++ show t ++ " = " ++ show (adjustShow x 0)

-- | Span show instance for error location display
instance Show Span where
  show span = "\n\x1b[1mLocation:\x1b[0m "
    ++ "\x1b[2m(line "++show (fst $ spanBeg span)++ ", column "++show (snd $ spanBeg span)++")\x1b[0m\n"
    ++ highlightError (spanBeg span) (spanEnd span) (spanSrc span)

-- | Error show instance using depth-aware disambiguation for better error messages
instance Show Error where
  show (CantInfer span ctx) = 
    "\x1b[1mCantInfer:\x1b[0m" ++
    "\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++
    show span
  show (Unsupported span ctx) = 
    "\x1b[1mUnsupported:\x1b[0m" ++
    "\nCurrently, Bend doesn't support matching on non-var expressions." ++
    "\nThis will be added later. For now, please split this definition." ++
    "\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++
    show span
  show (Undefined span ctx name) = 
    "\x1b[1mUndefined:\x1b[0m " ++ name ++
    "\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++
    show span
  show (TypeMismatch span ctx goal typ) = 
    "\x1b[1mMismatch:\x1b[0m" ++
    "\n- Goal: " ++ showAdjustedTerm goal ++ 
    "\n- Type: " ++ showAdjustedTerm typ ++
    "\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++
    show span
  show (TermMismatch span ctx a b) = 
    "\x1b[1mMismatch:\x1b[0m" ++
    "\n- " ++ showAdjustedTerm a ++ 
    "\n- " ++ showAdjustedTerm b ++
    "\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++
    show span
  show (IncompleteMatch span ctx) = 
    "\x1b[1mIncompleteMatch:\x1b[0m" ++
    "\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++
    show span
  show (UnknownTermination term) =
    "\x1b[1mUnknownTermination:\x1b[0m " ++ show term
  show (ImportError span msg) = 
    "\x1b[1mImportError:\x1b[0m " ++ msg ++
    show span

-- | Context show instance with duplicate name filtering
instance Show Ctx where
  show (Ctx ctx)
    | null lines = ""
    | otherwise  = init (unlines lines)
    where
      lines = map snd (reverse (clean S.empty (reverse (map showAnn ctx))))

      showAnn :: (Name,Term,Term) -> (Name,String)
      showAnn (k,_,t) = (k, "- " ++ k ++ " : " ++ show t)
    
      clean :: S.Set Name -> [(Name,String)] -> [(Name,String)]
      clean _    []                             = []
      clean seen ((n,l):xs) | n `S.member` seen = clean seen xs
                            | take 1 n == "_"   = clean seen xs
                            | otherwise         = (n,l) : clean (S.insert n seen) xs

-- ----------------------------- Show With Depth Disambiguation ------------------------------

-- | Shows a term with depth annotations only when variable names are shadowed
showAdjustedTerm :: Term -> String
showAdjustedTerm term = 
  let shadowedNames = findShadowed term
      adjusted = adjustShow term 0
  in if S.null shadowedNames
     then show term
     else showWithDepth shadowedNames adjusted 0

-- | Finds variable names that appear with different depths due to shadowing
findShadowed :: Term -> S.Set String
findShadowed term = S.fromList [k | (k, _) <- duplicates]
  where
    adjusted = adjustShow term 0
    vars = collectVars adjusted
    duplicates = findDuplicateNames vars
    
    -- | Find variable names that appear with different depths
    findDuplicateNames :: [(String, Int)] -> [(String, [Int])]
    findDuplicateNames vars = 
      let grouped = M.toList $ M.fromListWith (++) [(k, [i]) | (k, i) <- vars]
          uniqueDepths = [(k, S.toList $ S.fromList is) | (k, is) <- grouped]
      in [(k, ds) | (k, ds) <- uniqueDepths, length ds > 1]


-- | Replaces bound variables with their depth for HOAS disambiguation
adjustShow :: Term -> Int -> Term
adjustShow term depth = case term of
  -- Variables (no binding, just recurse)
  Var k i -> Var k i
  Ref k i -> Ref k i
  Sub t -> Sub (adjustShow t depth)

  -- Definitions with bindings
  Fix k f -> Fix k (\x -> adjustShow (f (Var k depth)) (depth + 1))
  Let k t v f -> Let k (fmap (`adjustShow` depth) t) (adjustShow v depth) (\x -> adjustShow (f (Var k depth)) (depth + 1))
  Use k v f -> Use k (adjustShow v depth) (\x -> adjustShow (f (Var k depth)) (depth + 1))

  -- Universe (no binding)
  Set -> Set

  -- Annotation (no binding, just recurse)
  Chk x t -> Chk (adjustShow x depth) (adjustShow t depth)

  -- Empty (no binding)
  Emp -> Emp
  EmpM -> EmpM

  -- Unit
  Uni -> Uni
  One -> One
  UniM f -> UniM (adjustShow f depth)

  -- Bool
  Bit -> Bit
  Bt0 -> Bt0
  Bt1 -> Bt1
  BitM f t -> BitM (adjustShow f depth) (adjustShow t depth)

  -- Nat
  Nat -> Nat
  Zer -> Zer
  Suc n -> Suc (adjustShow n depth)
  NatM z s -> NatM (adjustShow z depth) (adjustShow s depth)

  -- List
  Lst t -> Lst (adjustShow t depth)
  Nil -> Nil
  Con h t -> Con (adjustShow h depth) (adjustShow t depth)
  LstM n c -> LstM (adjustShow n depth) (adjustShow c depth)

  -- Enum
  Enu s -> Enu s
  Sym s -> Sym s
  EnuM cs d -> EnuM [(s, adjustShow t depth) | (s, t) <- cs] (adjustShow d depth)

  -- Numbers
  Num t -> Num t
  Val v -> Val v
  Op2 op a b -> Op2 op (adjustShow a depth) (adjustShow b depth)
  Op1 op a -> Op1 op (adjustShow a depth)

  -- Pair (Sig has a binding in the second component)
  Sig t f -> Sig (adjustShow t depth) (adjustShow f depth)
  Tup a b -> Tup (adjustShow a depth) (adjustShow b depth)
  SigM f -> SigM (adjustShow f depth)

  -- Function (All has a binding in the second component, Lam has a binding)
  All t f -> All (adjustShow t depth) (adjustShow f depth)
  Lam k t f -> Lam k (fmap (`adjustShow` depth) t) (\x -> adjustShow (f (Var k depth)) (depth + 1))
  App f a -> App (adjustShow f depth) (adjustShow a depth)

  -- Equality
  Eql t a b -> Eql (adjustShow t depth) (adjustShow a depth) (adjustShow b depth)
  Rfl -> Rfl
  EqlM f -> EqlM (adjustShow f depth)
  Rwt e f -> Rwt (adjustShow e depth) (adjustShow f depth)

  -- MetaVar
  Met n t ctx -> Met n (adjustShow t depth) (map (`adjustShow` depth) ctx)

  -- Superpositions
  Era -> Era
  Sup l a b -> Sup (adjustShow l depth) (adjustShow a depth) (adjustShow b depth)
  SupM l f -> SupM (adjustShow l depth) (adjustShow f depth)

  -- Errors
  Loc s t -> Loc s (adjustShow t depth)

  -- Logging
  Log s x -> Log (adjustShow s depth) (adjustShow x depth)

  -- Primitive
  Pri p -> Pri p

  -- Sugars
  Pat ts ms cs -> Pat (map (`adjustShow` depth) ts) 
                      [(k, adjustShow v depth) | (k, v) <- ms]
                      [([adjustShow p depth | p <- ps], adjustShow t depth) | (ps, t) <- cs]
  Frk l a b -> Frk (adjustShow l depth) (adjustShow a depth) (adjustShow b depth)

-- | Shows a term with depth annotations only for shadowed variable names
showWithDepth :: S.Set String -> Term -> Int -> String
showWithDepth shadowed trm depth = case trm of
  -- Variables show their depth only if the name is shadowed
  Var k i -> if S.member k shadowed 
             then k ++ "^" ++ show i
             else k
  Ref k i -> k
  Sub t -> showWithDepth shadowed t depth
  
  -- Definitions with bindings - show depth only if name is shadowed
  Fix k f -> 
    let kStr = if S.member k shadowed then k ++ "^" ++ show depth else k
    in "μ" ++ kStr ++ ". " ++ showWithDepth shadowed (f (Var k depth)) (depth + 1)
  Let k t v f -> 
    let kStr = if S.member k shadowed then k ++ "^" ++ show depth else k
    in case t of
      Just t  -> kStr ++ " : " ++ showWithDepth shadowed t depth ++ " = " ++ showWithDepth shadowed v depth ++ " " ++ showWithDepth shadowed (f (Var k depth)) (depth + 1)
      Nothing -> kStr ++ " = " ++ showWithDepth shadowed v depth ++ " " ++ showWithDepth shadowed (f (Var k depth)) (depth + 1)
  Use k v f -> 
    let kStr = if S.member k shadowed then k ++ "^" ++ show depth else k
    in "use " ++ kStr ++ " = " ++ showWithDepth shadowed v depth ++ " " ++ showWithDepth shadowed (f (Var k depth)) (depth + 1)
  
  -- No binding terms - same as show but recurse with showWithDepth
  Set -> "Set"
  Chk x t -> "(" ++ showWithDepth shadowed x depth ++ "::" ++ showWithDepth shadowed t depth ++ ")"
  Emp -> "Empty"
  EmpM -> "λ{}"
  Uni -> "Unit"
  One -> "()"
  UniM f -> "λ{():" ++ showWithDepth shadowed f depth ++ "}"
  Bit -> "Bool"
  Bt0 -> "False"
  Bt1 -> "True"
  BitM f t -> "λ{False:" ++ showWithDepth shadowed f depth ++ ";True:" ++ showWithDepth shadowed t depth ++ "}"
  Nat -> "Nat"
  Zer -> "0n"
  term@(Suc _) ->
    let (k, rest) = count term in
    case cut rest of
      Zer -> show k ++ "n"
      _   -> show k ++ "n+" ++ showWithDepth shadowed rest depth
    where count :: Term -> (Int, Term)
          count (cut -> Suc t) = let (c, r) = count t in (c + 1, r)
          count t              = (0, t)
  NatM z s -> "λ{0n:" ++ showWithDepth shadowed z depth ++ ";1n+:" ++ showWithDepth shadowed s depth ++ "}"
  Lst t -> showWithDepth shadowed t depth ++ "[]"
  Nil -> "[]"
  Con h t -> fromMaybe (showWithDepth shadowed h depth ++ "<>" ++ showWithDepth shadowed t depth) (prettyStrDepth (Con h t) depth)
  LstM n c -> "λ{[]:" ++ showWithDepth shadowed n depth ++ ";<>:" ++ showWithDepth shadowed c depth ++ "}"
  Enu s -> "enum{" ++ intercalate "," (map (\x -> "&" ++ x) s) ++ "}"
  Sym s -> "&" ++ s
  EnuM c e -> "λ{" ++ intercalate ";" (map (\(s,t) -> "&" ++ s ++ ":" ++ showWithDepth shadowed t depth) c) ++ ";" ++ showWithDepth shadowed e depth ++ "}"
  
  -- Sig and All with binder depth annotations
  Sig a b -> case cut b of
    Lam "_" t f -> showArgDepth a ++ " & " ++ showCodomainDepth (f (Var "_" depth))
    Lam k t f   -> 
      let kStr = if S.member k shadowed then k ++ "^" ++ show depth else k
      in "Σ" ++ kStr ++ ":" ++ showArgDepth a ++ ". " ++ showWithDepth shadowed (f (Var k depth)) (depth + 1)
    _           -> "Σ" ++ showArgDepth a ++ ". " ++ showWithDepth shadowed b depth
    where
      showArgDepth t = case cut t of
        All{} -> "(" ++ showWithDepth shadowed t depth ++ ")"
        Sig{} -> "(" ++ showWithDepth shadowed t depth ++ ")"
        _     -> showWithDepth shadowed t depth
      showCodomainDepth t = case t of
        Sig _ (Lam k _ _) | k /= "_" -> "(" ++ showWithDepth shadowed t (depth + 1) ++ ")"
        _                             -> showWithDepth shadowed t (depth + 1)
  
  All a b -> case b of
    Lam "_" t f -> showArgDepth a ++ " -> " ++ showCodomainDepth (f (Var "_" depth))
    Lam k t f   -> 
      let kStr = if S.member k shadowed then k ++ "^" ++ show depth else k
      in "∀" ++ kStr ++ ":" ++ showArgDepth a ++ ". " ++ showWithDepth shadowed (f (Var k depth)) (depth + 1)
    _           -> "∀" ++ showArgDepth a ++ ". " ++ showWithDepth shadowed b depth
    where
      showArgDepth t = case cut t of
        All{} -> "(" ++ showWithDepth shadowed t depth ++ ")"
        Sig{} -> "(" ++ showWithDepth shadowed t depth ++ ")"
        _     -> showWithDepth shadowed t depth
      showCodomainDepth t = case t of
        All _ (Lam k _ _) | k /= "_" -> "(" ++ showWithDepth shadowed t (depth + 1) ++ ")"
        _                             -> showWithDepth shadowed t (depth + 1)
  
  Lam k t f -> 
    let kStr = if S.member k shadowed then k ++ "^" ++ show depth else k
    in case t of
      Just t  -> "λ" ++ kStr ++ ":" ++ showWithDepth shadowed t depth ++ ". " ++ showWithDepth shadowed (f (Var k depth)) (depth + 1)
      Nothing -> "λ" ++ kStr ++ ". " ++ showWithDepth shadowed (f (Var k depth)) (depth + 1)
  
  app@(App _ _) -> fnStr ++ "(" ++ intercalate "," (map (\arg -> showWithDepth shadowed arg depth) args) ++ ")" where
    (fn, args) = collectApps app []
    fnStr      = case cut fn of
      Var k i -> showWithDepth shadowed (Var k i) depth
      Ref k i -> showWithDepth shadowed (Ref k i) depth
      fn      -> "(" ++ showWithDepth shadowed fn depth ++ ")"
  
  Tup a b -> "(" ++ intercalate "," (map (\t -> showWithDepth shadowed t depth) (flattenTup trm)) ++ ")"
  SigM f -> "λ{(,):" ++ showWithDepth shadowed f depth ++ "}"
  
  Eql t a b -> case t of
    (Sig _ _) -> "(" ++ showWithDepth shadowed t depth ++ ")" ++ "{" ++ showWithDepth shadowed a depth ++ "==" ++ showWithDepth shadowed b depth ++ "}"
    (All _ _) -> "(" ++ showWithDepth shadowed t depth ++ ")" ++ "{" ++ showWithDepth shadowed a depth ++ "==" ++ showWithDepth shadowed b depth ++ "}"
    _         -> showWithDepth shadowed t depth ++ "{" ++ showWithDepth shadowed a depth ++ "==" ++ showWithDepth shadowed b depth ++ "}"
  Rfl -> "{==}"
  EqlM f -> "λ{{==}:" ++ showWithDepth shadowed f depth ++ "}"
  Rwt e f -> "rewrite " ++ showWithDepth shadowed e depth ++ " " ++ showWithDepth shadowed f depth
  
  Met n t ctx -> "?" ++ n ++ ":" ++ showWithDepth shadowed t depth ++ "{" ++ intercalate "," (map (\c -> showWithDepth shadowed c depth) ctx) ++ "}"
  Era -> "*"
  Sup l a b -> "&" ++ showWithDepth shadowed l depth ++ "{" ++ showWithDepth shadowed a depth ++ "," ++ showWithDepth shadowed b depth ++ "}"
  SupM l f -> "λ{&" ++ showWithDepth shadowed l depth ++ "{,}:" ++ showWithDepth shadowed f depth ++ "}"
  
  Loc _ t -> showWithDepth shadowed t depth
  Log s x -> "log " ++ showWithDepth shadowed s depth ++ " " ++ showWithDepth shadowed x depth
  Pri p -> pri p where
    pri U64_TO_CHAR = "U64_TO_CHAR"
    pri CHAR_TO_U64 = "CHAR_TO_U64"
    pri HVM_INC = "HVM_INC"
    pri HVM_DEC = "HVM_DEC"
  
  Num U64_T -> "U64"
  Num I64_T -> "I64"
  Num F64_T -> "F64"
  Num CHR_T -> "Char"
  Val (U64_V n) -> show n
  Val (I64_V n) -> if n >= 0 then "+" ++ show n else show n
  Val (F64_V n) -> show n
  Val (CHR_V c) -> "'" ++ showChar c ++ "'" where
    showChar '\n' = "\\n"
    showChar '\t' = "\\t"
    showChar '\r' = "\\r"
    showChar '\0' = "\\0"
    showChar '\\' = "\\\\"
    showChar '\'' = "\\'"
    showChar c    = [c]
  
  Op2 ADD a b -> "(" ++ showWithDepth shadowed a depth ++ " + " ++ showWithDepth shadowed b depth ++ ")"
  Op2 SUB a b -> "(" ++ showWithDepth shadowed a depth ++ " - " ++ showWithDepth shadowed b depth ++ ")"
  Op2 MUL a b -> "(" ++ showWithDepth shadowed a depth ++ " * " ++ showWithDepth shadowed b depth ++ ")"
  Op2 DIV a b -> "(" ++ showWithDepth shadowed a depth ++ " / " ++ showWithDepth shadowed b depth ++ ")"
  Op2 MOD a b -> "(" ++ showWithDepth shadowed a depth ++ " % " ++ showWithDepth shadowed b depth ++ ")"
  Op2 EQL a b -> "(" ++ showWithDepth shadowed a depth ++ " == " ++ showWithDepth shadowed b depth ++ ")"
  Op2 NEQ a b -> "(" ++ showWithDepth shadowed a depth ++ " !== " ++ showWithDepth shadowed b depth ++ ")"
  Op2 LST a b -> "(" ++ showWithDepth shadowed a depth ++ " < " ++ showWithDepth shadowed b depth ++ ")"
  Op2 GRT a b -> "(" ++ showWithDepth shadowed a depth ++ " > " ++ showWithDepth shadowed b depth ++ ")"
  Op2 LEQ a b -> "(" ++ showWithDepth shadowed a depth ++ " <= " ++ showWithDepth shadowed b depth ++ ")"
  Op2 GEQ a b -> "(" ++ showWithDepth shadowed a depth ++ " >= " ++ showWithDepth shadowed b depth ++ ")"
  Op2 AND a b -> "(" ++ showWithDepth shadowed a depth ++ " && " ++ showWithDepth shadowed b depth ++ ")"
  Op2 OR a b  -> "(" ++ showWithDepth shadowed a depth ++ " | " ++ showWithDepth shadowed b depth ++ ")"
  Op2 XOR a b -> "(" ++ showWithDepth shadowed a depth ++ " ^ " ++ showWithDepth shadowed b depth ++ ")"
  Op2 SHL a b -> "(" ++ showWithDepth shadowed a depth ++ " << " ++ showWithDepth shadowed b depth ++ ")"
  Op2 SHR a b -> "(" ++ showWithDepth shadowed a depth ++ " >> " ++ showWithDepth shadowed b depth ++ ")"
  Op2 POW a b -> "(" ++ showWithDepth shadowed a depth ++ " ** " ++ showWithDepth shadowed b depth ++ ")"
  Op1 NOT a -> "(not " ++ showWithDepth shadowed a depth ++ ")"
  Op1 NEG a -> "(-" ++ showWithDepth shadowed a depth ++ ")"
  
  Pat ts ms cs -> "match " ++ unwords (map (\t -> showWithDepth shadowed t depth) ts) ++ " {" ++ showMoves ++ showCases ++ " }" where
    showMoves = if null ms then "" else " with " ++ intercalate " with " (map mv ms) where
      mv(k,x) = k ++ "=" ++ showWithDepth shadowed x depth
    showCases = if null cs then "" else " " ++ intercalate " " (map showCase cs) where
      showCase(ps,x) = "case " ++ unwords (map showPat ps) ++ ": " ++ showWithDepth shadowed x depth
      showPat p = "(" ++ showWithDepth shadowed p depth ++ ")"
  
  Frk l a b -> "fork " ++ showWithDepth shadowed l depth ++ ":" ++ showWithDepth shadowed a depth ++ " else:" ++ showWithDepth shadowed b depth

-- | Helper for pretty-printing strings with proper depth context
prettyStrDepth :: Term -> Int -> Maybe String
prettyStrDepth = go [] where
  go :: [Char] -> Term -> Int -> Maybe String
  go acc Nil _ = Just ("\"" ++ reverse acc ++ "\"")
  go acc (Con (Val (CHR_V c)) rest) d = go (c:acc) rest d
  go acc (Loc _ t) d = go acc t d
  go _ _ _ = Nothing


-- ----------------------------------- Helper Functions ------------------------------------

-- | Helper for pretty-printing character lists as strings
prettyStr :: Term -> Maybe String
prettyStr = go [] where
  go :: [Char] -> Term -> Maybe String
  go acc Nil                        = Just ("\"" ++ reverse acc ++ "\"")
  go acc (Con (Val (CHR_V c)) rest) = go (c:acc) rest
  go acc (Loc _ t)                  = go acc t
  go _   _                          = Nothing

-- | Helper for pretty-printing constructor tuples
prettyCtr :: Term -> Maybe String
prettyCtr (Tup (Sym name) rest) = 
  case lastElem rest of
    Just One -> Just ("@" ++ name ++ "{" ++ intercalate "," (map show (init (flattenTup rest))) ++ "}")
    _        -> Nothing
  where lastElem (Tup _ r) = lastElem r
        lastElem t         = Just t
prettyCtr _ = Nothing

-- | Error function for span-based error reporting
errorWithSpan :: Span -> String -> a
errorWithSpan span msg = unsafePerformIO $ do
  hPutStrLn stderr $ msg
  hPutStrLn stderr $ (show span)
  exitFailure