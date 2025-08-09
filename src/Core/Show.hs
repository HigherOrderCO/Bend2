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
  show tup@(Tup _ _)  = "(" ++ intercalate "," (map show (flattenTup tup)) ++ ")"
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
    (Sig _ _) -> "(" ++ show t ++ "){" ++ show a ++ "==" ++ show b ++ "}"
    (All _ _) -> "(" ++ show t ++ "){" ++ show a ++ "==" ++ show b ++ "}"
    _         ->        show t ++        "{" ++ show a ++ "==" ++ show b ++ "}"
  show (Rfl)           = "{==}"
  show (EqlM f)        = "λ{{==}:" ++ show f ++ "}"
  show (Rwt e f)       = "rewrite " ++ show e ++ " " ++ show f
  show (ADT name params) = if null params 
                           then name
                           else name ++ "<" ++ intercalate "," (map show params) ++ ">"
  show (Ctr name args)   = name ++ "{" ++ intercalate "," (map show args) ++ "}"
  show (ADTM name cases defCase) = "λ" ++ name ++ "{" ++ intercalate ";" (map showCase cases ++ maybeDefault) ++ "}"
    where
      showCase (k, f) = k ++ "{}:" ++ show f
      maybeDefault = case defCase of
        Just d  -> ["{}:" ++ show d]
        Nothing -> []
  show (Met n t ctx)   = "?" ++ n ++ ":" ++ show t ++ "{" ++ intercalate "," (map show ctx) ++ "}"
  show (Era)           = "*"
  show (Sup l a b)     = "&" ++ show l ++ "{" ++ show a ++ "," ++ show b ++ "}"
  show (SupM l f)      = "λ{&" ++ show l ++ "{,}:" ++ show f ++ "}"
  show (Loc _ t)       = show t
  show (Log s x)       = "log " ++ show s ++ " " ++ show x
  show (Pri p)         = pri p where
    pri U64_TO_CHAR    = "U64_TO_CHAR"
    pri CHAR_TO_U64    = "CHAR_TO_U64"
    pri HVM_INC        = "HVM_INC"
    pri HVM_DEC        = "HVM_DEC"
  show (Pat t m c)     = "match " ++ unwords (map show t) ++ " {" ++ showMoves ++ showCases ++ " }" where
             showMoves = if null m then "" else " with " ++ intercalate " with " (map mv m) where
               mv(k,x) = k ++ "=" ++ show x
             showCases = if null c then "" else " " ++ intercalate " " (map cs c) where
               cs(p,x) = "case " ++ unwords (map showPat p) ++ ": " ++ show x
             showPat p = "(" ++ show p ++ ")"
  show (Frk l a b)     = "fork " ++ show l ++ ":" ++ show a ++ " else:" ++ show b

instance Show Book where
  show (Book funs adts names) = unlines (map showDef names)
    where
      showDef name = case M.lookup name funs of
        Just (Function _ t b) -> name ++ " : " ++ show t ++ " = " ++ show b
        Nothing -> case M.lookup name adts of
          Just adt -> showADT adt
          Nothing  -> ""
      showADT (DataType name typ ctrs) = 
        "type " ++ name ++ " : " ++ show typ ++ "\n" ++
        unlines (map showCtr ctrs)
      showCtr (name, _) = "  case " ++ name ++ "{}: ..."

instance Show Span where
  show span = "\n\x1b[1mLocation:\x1b[0m "
    ++ "\x1b[2m(line "++show (fst $ spanBeg span)++ ", column "++show (snd $ spanBeg span)++")\x1b[0m\n"
    ++ highlightError (spanBeg span) (spanEnd span) (spanSrc span)

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
    "\n- Goal: " ++ show goal ++ 
    "\n- Type: " ++ show typ ++
    "\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++
    show span
  show (TermMismatch span ctx a b) = 
    "\x1b[1mMismatch:\x1b[0m" ++
    "\n- " ++ show a ++ 
    "\n- " ++ show b ++
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

-- Helper functions used by Show instances
flattenTup :: Term -> [Term]
flattenTup (Tup a b) = a : flattenTup b
flattenTup t         = [t]

prettyStr :: Term -> Maybe String
prettyStr = go [] where
  go :: [Char] -> Term -> Maybe String
  go acc Nil                        = Just ("\"" ++ reverse acc ++ "\"")
  go acc (Con (Val (CHR_V c)) rest) = go (c:acc) rest
  go acc (Loc _ t)                  = go acc t
  go _   _                          = Nothing

prettyCtr :: Term -> Maybe String
prettyCtr (Ctr name args) = Just (name ++ "{" ++ intercalate "," (map show args) ++ "}")
prettyCtr _               = Nothing

errorWithSpan :: Span -> String -> a
errorWithSpan span msg = unsafePerformIO $ do
  hPutStrLn stderr $ msg
  hPutStrLn stderr $ (show span)
  exitFailure

warnWithSpan :: Span -> String -> ()
warnWithSpan span msg = unsafePerformIO $ do
  hPutStrLn stderr $ "Warning: " ++ msg
  hPutStrLn stderr $ (show span)
  return ()
