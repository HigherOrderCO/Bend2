{-./Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Show where

import Core.Type
import Control.Exception (Exception)
import qualified Data.Map as M
import Data.List (intercalate)
import Data.Maybe (fromMaybe)
import Highlight (highlightError)

import System.Exit
import System.IO
import System.IO.Unsafe (unsafePerformIO)

-- Simple term display with no shadowing or prefix logic
showTerm :: Bool -> Term -> String
showTerm _ term = showPlain term 0

showPlain :: Term -> Int -> String
showPlain term depth = case term of
  Var k i      -> showVar k i
  Ref k _      -> k
  Sub t        -> showPlain t depth
  Fix k f      -> "μ" ++ k ++ ". " ++ showPlain (f (Var k depth)) (depth + 1)
  Let k t v f  -> showLet k t v f depth
  Use k v f    -> "use " ++ k ++ " = " ++ showPlain v depth ++ " " ++ showPlain (f (Var k depth)) (depth + 1)
  Set          -> "Set"
  Chk x t      -> "(" ++ showPlain x depth ++ "::" ++ showPlain t depth ++ ")"
  Tst x        -> "trust " ++ showPlain x depth
  Emp          -> "Empty"
  EmpM         -> "λ{}"
  Uni          -> "Unit"
  One          -> "()"
  UniM f       -> "λ{():" ++ showPlain f depth ++ "}"
  Bit          -> "Bool"
  Bt0          -> "False"
  Bt1          -> "True"
  BitM f t     -> "λ{False:" ++ showPlain f depth ++ ";True:" ++ showPlain t depth ++ "}"
  Nat          -> "Nat"
  Zer          -> "0n"
  Suc _        -> showSuc term depth
  NatM z s     -> "λ{0n:" ++ showPlain z depth ++ ";1n+:" ++ showPlain s depth ++ "}"
  Lst t        -> showPlain t depth ++ "[]"
  Nil          -> "[]"
  Con h t      -> showCon h t depth
  LstM n c     -> "λ{[]:" ++ showPlain n depth ++ ";<>:" ++ showPlain c depth ++ "}"
  Enu s        -> "enum{" ++ intercalate "," (map ("&" ++) s) ++ "}"
  Sym s        -> "&" ++ s
  EnuM cs d    -> showEnuM cs d depth
  Sig a b      -> showSig a b depth
  Tup _ _      -> showTup term depth
  SigM f       -> "λ{(,):" ++ showPlain f depth ++ "}"
  All a b      -> showAll a b depth
  Lam k t f    -> showLam k t f depth
  App _ _      -> showApp term depth
  Eql t a b    -> showEql t a b depth
  Rfl          -> "{==}"
  EqlM f       -> "λ{{==}:" ++ showPlain f depth ++ "}"
  Rwt e f      -> "rewrite " ++ showPlain e depth ++ " " ++ showPlain f depth
  Met n t ctx  -> "?" ++ n ++ ":" ++ showPlain t depth ++ "{" ++ intercalate "," (map (\c -> showPlain c depth) ctx) ++ "}"
  Era          -> "*"
  Sup l a b    -> "&" ++ showPlain l depth ++ "{" ++ showPlain a depth ++ "," ++ showPlain b depth ++ "}"
  SupM l f     -> "λ{&" ++ showPlain l depth ++ "{,}:" ++ showPlain f depth ++ "}"
  Loc _ t      -> showPlain t depth
  Log s x      -> "log " ++ showPlain s depth ++ " " ++ showPlain x depth
  Pri p        -> showPri p
  Num t        -> showNum t
  Val v        -> showVal v
  Op2 o a b    -> showOp2 o a b depth
  Op1 o a      -> showOp1 o a depth
  Pat ts ms cs -> showPat ts ms cs depth
  Frk l a b    -> "fork " ++ showPlain l depth ++ ":" ++ showPlain a depth ++ " else:" ++ showPlain b depth
  IO t         -> "IO<" ++ showPlain t depth ++ ">"

showVar :: String -> Int -> String
showVar k _ = k

showLet :: String -> Maybe Term -> Term -> Body -> Int -> String
showLet k mt v f depth = case mt of
  Just t  -> k ++ " : " ++ showPlain t depth ++ " = " ++ showPlain v depth ++ " " ++ showPlain (f (Var k depth)) (depth + 1)
  Nothing -> k ++ " = " ++ showPlain v depth ++ " " ++ showPlain (f (Var k depth)) (depth + 1)

showSuc :: Term -> Int -> String
showSuc term depth = case count term of
  (k, Zer) -> show (k :: Integer) ++ "n"
  (k, r)   -> show (k :: Integer) ++ "n+" ++ showPlain r depth
  where
    count (cut -> Suc t) = let (c, r) = count t in (c + 1, r)
    count t              = (0 :: Integer, t)

showCon :: Term -> Term -> Int -> String
showCon h t depth = fromMaybe plain (showStr (Con h t) depth)
  where plain = showPlain h depth ++ "<>" ++ showPlain t depth

showEnuM :: [(String,Term)] -> Term -> Int -> String
showEnuM cs d depth = "λ{" ++ intercalate ";" cases ++ ";" ++ showPlain d depth ++ "}"
  where cases = map (\(s,t) -> "&" ++ s ++ ":" ++ showPlain t depth) cs

showSig :: Term -> Term -> Int -> String
showSig a b depth = case cut b of
  Lam "_" _ f -> "(" ++ showPlain a depth ++ " & " ++ showPlain (f (Var "_" depth)) (depth + 1) ++ ")"
  Lam k _ f   -> "Σ" ++ k ++ ":" ++ showPlain a depth ++ ". " ++ showPlain (f (Var k depth)) (depth + 1)
  _           -> "Σ" ++ showPlain a depth ++ ". " ++ showPlain b depth

showAll :: Term -> Term -> Int -> String
showAll a b depth = case b of
  Lam "_" _ f -> showPlain a depth ++ " -> " ++ showPlain (f (Var "_" depth)) (depth + 1)
  Lam k _ f   -> "∀" ++ k ++ ":" ++ showPlain a depth ++ ". " ++ showPlain (f (Var k depth)) (depth + 1)
  _           -> "∀" ++ showPlain a depth ++ ". " ++ showPlain b depth

showLam :: String -> Maybe Term -> Body -> Int -> String
showLam k mt f depth = case mt of
  Just t  -> "λ" ++ k ++ ":" ++ showPlain t depth ++ ". " ++ showPlain (f (Var k depth)) (depth + 1)
  Nothing -> "λ" ++ k ++ ". " ++ showPlain (f (Var k depth)) (depth + 1)

showApp :: Term -> Int -> String
showApp term depth = fnStr ++ "(" ++ intercalate "," (map (\arg -> showPlain arg depth) args) ++ ")"
  where
    (fn, args) = collectApps term []
    fnStr = case cut fn of
      Var k i -> showVar k i
      Ref k _ -> k
      _       -> "(" ++ showPlain fn depth ++ ")"

showTup :: Term -> Int -> String
showTup term depth = fromMaybe plain (showCtr term)
  where plain = "(" ++ intercalate "," (map (\t -> showPlain t depth) (flattenTup term)) ++ ")"

showEql :: Term -> Term -> Term -> Int -> String
showEql t a b depth = typeStr ++ "{" ++ showPlain a depth ++ "==" ++ showPlain b depth ++ "}"
  where
    typeStr = case t of
      Sig _ _ -> "(" ++ showPlain t depth ++ ")"
      All _ _ -> "(" ++ showPlain t depth ++ ")"
      _       -> showPlain t depth

showOp2 :: NOp2 -> Term -> Term -> Int -> String
showOp2 op a b depth = "(" ++ showPlain a depth ++ " " ++ opStr ++ " " ++ showPlain b depth ++ ")"
  where
    opStr = case op of
      ADD -> "+";   SUB -> "-";   MUL -> "*";   DIV -> "/"
      MOD -> "%";   POW -> "**";  EQL -> "==";  NEQ -> "!=="
      LST -> "<";    GRT -> ">";   LEQ -> "<=";  GEQ -> ">="
      AND -> "&&";   OR  -> "|";   XOR -> "^"
      SHL -> "<<";   SHR -> ">>"

showOp1 :: NOp1 -> Term -> Int -> String
showOp1 op a depth = case op of
  NOT -> "(not " ++ showPlain a depth ++ ")"
  NEG -> "(-" ++ showPlain a depth ++ ")"

showPat :: [Term] -> [Move] -> [Case] -> Int -> String
showPat ts ms cs depth = "match " ++ unwords (map (\t -> showPlain t depth) ts) ++ " {" ++ moves ++ cases ++ " }"
  where
    moves = case ms of
      [] -> ""
      _  -> " with " ++ intercalate " with " (map showMove ms)
    cases = case cs of
      [] -> ""
      _  -> " " ++ intercalate " " (map showCase cs)
    showMove (k,x)   = k ++ "=" ++ showPlain x depth
    showCase (ps,x)  = "case " ++ unwords (map showPat' ps) ++ ": " ++ showPlain x depth
    showPat' p       = "(" ++ showPlain p depth ++ ")"

showPri :: PriF -> String
showPri p = case p of
  U64_TO_CHAR   -> "U64_TO_CHAR"
  CHAR_TO_U64   -> "CHAR_TO_U64"
  HVM_INC       -> "HVM_INC"
  HVM_DEC       -> "HVM_DEC"
  IO_PRINT      -> "IO_PRINT"
  IO_PUTC       -> "IO_PUTC"
  IO_GETC       -> "IO_GETC"
  IO_READ_FILE  -> "IO_READ_FILE"
  IO_WRITE_FILE -> "IO_WRITE_FILE"
  IO_BIND       -> "IO_BIND"
  IO_PURE       -> "IO_PURE"

showNum :: NTyp -> String
showNum t = case t of
  U64_T -> "U64"
  I64_T -> "I64"
  F64_T -> "F64"
  CHR_T -> "Char"

showVal :: NVal -> String
showVal v = case v of
  U64_V n -> show n
  I64_V n -> show n
  F64_V n -> show n
  CHR_V c -> "'" ++ showCharLit c ++ "'"

showCharLit :: Char -> String
showCharLit c = case c of
  '\n' -> "\\n";  '\t' -> "\\t";  '\r' -> "\\r";  '\0' -> "\\0"
  '\\' -> "\\\\"; '\'' -> "\\'"
  _    -> [c]

showStr :: Term -> Int -> Maybe String
showStr term depth = go [] term
  where
    go acc Nil                        = Just ("\"" ++ reverse acc ++ "\"")
    go acc (Con (Val (CHR_V c)) rest) = go (c:acc) rest
    go acc (Loc _ t)                  = go acc t
    go _   _                          = Nothing

showCtr :: Term -> Maybe String
showCtr t = case flattenTup t of
  (Sym name : xs) -> Just ("@" ++ name ++ "{" ++ intercalate "," (map show xs) ++ "}")
  _               -> Nothing

showHint :: Maybe String -> String
showHint Nothing = ""
showHint (Just h) = "\x1b[1mHint:\x1b[0m " ++ h ++ "\n"

instance Show Term where
  show = showTerm False

instance Show Book where
  show (Book defs names) = unlines [showDefn name (defs M.! name) | name <- names]
    where showDefn k (_, x, t) = k ++ " : " ++ show t ++ " = " ++ showTerm True x

instance Show Span where
  show span = "\n\x1b[1mLocation:\x1b[0m \x1b[2m(line " ++ show (fst $ spanBeg span) ++ ", column " ++ show (snd $ spanBeg span) ++ ")\x1b[0m\n" ++ highlightError (spanBeg span) (spanEnd span) (spanSrc span)

instance Show Error where
  show err = case err of
    CantInfer span ctx hint       -> "\x1b[1mCantInfer:\x1b[0m\n" ++ showHint hint ++ "\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span
    Unsupported span ctx hint     -> "\x1b[1mUnsupported:\x1b[0m\nCurrently, Bend doesn't support matching on non-var expressions.\nThis will be added later. For now, please split this definition.\n" ++ showHint hint ++ "\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span
    Undefined span ctx name hint  -> "\x1b[1mUndefined:\x1b[0m " ++ name ++ "\n" ++ showHint hint ++ "\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span
    TypeMismatch span ctx goal typ hint -> "\x1b[1mMismatch:\x1b[0m\n- Goal: " ++ showTerm True goal ++ "\n- Type: " ++ showTerm True typ ++ "\n" ++ showHint hint ++ "\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span
    TermMismatch span ctx a b hint -> "\x1b[1mMismatch:\x1b[0m\n- " ++ showTerm True a ++ "\n- " ++ showTerm True b ++ "\n" ++ showHint hint ++ "\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span
    IncompleteMatch span ctx hint -> "\x1b[1mIncompleteMatch:\x1b[0m\n" ++ showHint hint ++ "\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span
    UnknownTermination term       -> "\x1b[1mUnknownTermination:\x1b[0m " ++ show term
    ImportError span msg          -> "\x1b[1mImportError:\x1b[0m " ++ msg ++ show span
    AmbiguousEnum span ctx ctor fqns hint -> "\x1b[1mAmbiguousEnum:\x1b[0m &" ++ ctor ++ "\nCould be:\n" ++ unlines ["  - &" ++ fqn | fqn <- fqns] ++ showHint hint ++ "\x1b[1mContext:\x1b[0m\n" ++ show ctx ++ show span
    CompilationError msg          -> "\x1b[1mCompilationError:\x1b[0m " ++ msg

newtype BendException = BendException Error

instance Show BendException where
  show (BendException e) = show e

instance Exception BendException

instance Show Ctx where
  show (Ctx ctx) = case lines of
    [] -> ""
    _  -> init (unlines lines)
    where
      lines = map snd (reverse (clean [] (reverse (map showAnn ctx))))
      showAnn (k, _, t) = (k, "- " ++ k ++ " : " ++ show t)
      clean seen [] = []
      clean seen ((n,l):xs)
        | n `elem` seen = clean seen xs
        | take 1 n == "_"   = clean seen xs
        | otherwise         = (n,l) : clean (n:seen) xs

errorWithSpan :: Span -> String -> a
errorWithSpan span msg = unsafePerformIO $ do
  hPutStrLn stderr msg
  hPutStrLn stderr (show span)
  exitFailure
