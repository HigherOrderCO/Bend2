{-./Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Show where

import Core.Type
import Control.Exception (Exception)
import qualified Data.Map as M
import Data.List (intercalate, unsnoc)
import Data.List.Split (splitOn)
import Highlight (highlightError)

import Debug.Trace
import System.Exit
import System.IO
import System.IO.Unsafe (unsafePerformIO)

-- Simple term display with no shadowing or prefix logic
showTerm :: Bool -> Term -> String
showTerm _ term = go 0 M.empty term
  where
    showName vars k i = case M.lookup k vars of
      Just j | i < j -> k ++ "^" ++ show i
      _              -> k

    go :: Int -> M.Map Name Int -> Term -> String
    go d vars term = case term of
      -- Variables
      Var k i      -> showName vars k i
      Ref k _      -> shortName k
      Sub t        -> go d vars t

      -- IO type
      IO t         -> "IO<" ++ go d vars t ++ ">"

      -- Definitions
      Fix k f      -> "μ" ++ k ++ ". " ++ go (d+1) vars (f (Var k d))
      Let k mt v f -> case mt of
        Just t  -> k ++ " : " ++ go d vars t ++ " = " ++ go d vars v ++ " " ++ go (d+1) vars (f (Var k d))
        Nothing -> k ++                         " = " ++ go d vars v ++ " " ++ go (d+1) vars (f (Var k d))
      Use k v f    -> "use " ++ k ++ " = " ++ go d vars v ++ " " ++ go (d+1) vars (f (Var k d))

      -- Universe
      Set          -> "Set"

      -- Annotation
      Chk x t      -> "(" ++ go d vars x ++ "::" ++ go d vars t ++ ")"
      Tst x        -> "trust " ++ go d vars x

      -- Empty
      Emp          -> "Empty"
      EmpM         -> "λ{}"

      -- Unit
      Uni          -> "Unit"
      One          -> "()"
      UniM f       -> "λ{():" ++ go d vars f ++ "}"

      -- Bool
      Bit          -> "Bool"
      Bt0          -> "False"
      Bt1          -> "True"
      BitM f t     -> "λ{False:" ++ go d vars f ++ "; True:" ++ go d vars t ++ "}"

      -- Nat
      Nat          -> "Nat"
      Zer          -> "0n"
      Suc _        -> case count term of
        (k, Zer) -> show (k :: Integer) ++ "n"
        (k, r)   -> show (k :: Integer) ++ "n+" ++ go d vars r
        where
          count (cut -> Suc t) = let (c, r) = count t in (c + 1, r)
          count t              = (0 :: Integer, t)
      NatM z s     -> "λ{0n:" ++ go d vars z ++ ";1n+:" ++ go d vars s ++ "}"

      -- List
      Lst t        -> go d vars t ++ "[]"
      Nil          -> "[]"
      Con h t      ->
        let plain = go d vars h ++ "<>" ++ go d vars t
            go' acc Nil                        = Just ("\"" ++ reverse acc ++ "\"")
            go' acc (Con (Val (CHR_V c)) rest) = go' (c : acc) rest
            go' acc (Loc _ t')                 = go' acc t'
            go' _   _                          = Nothing
        in case go' [] (Con h t) of
             Just str -> str
             Nothing  -> plain
      LstM n c     -> "λ{[]:" ++ go d vars n ++ ";<>:" ++ go d vars c ++ "}"

      -- Enum
      Enu s        -> "enum{" ++ intercalate "," (map (("&" ++) . shortName) s) ++ "}"
      Sym s        -> "&" ++ shortName s
      EnuM cs d'   -> "λ{" ++ intercalate ";" cases ++ ";" ++ go d vars d' ++ "}"
        where
          cases = map (\(s,t) -> "&" ++ shortName s ++ ":" ++ go d vars t) cs

      -- Numbers
      Num t        -> case t of
        U64_T -> "U64"
        I64_T -> "I64"
        F64_T -> "F64"
        CHR_T -> "Char"
      Val v        -> case v of
        U64_V n -> show n
        I64_V n -> show n
        F64_V n -> show n
        CHR_V c -> "'" ++ (case c of
          '\n' -> "\\n";  '\t' -> "\\t";  '\r' -> "\\r";  '\0' -> "\\0"
          '\\' -> "\\\\"; '\'' -> "\\'"
          _    -> [c]) ++ "'"
      Op2 o a b    -> "(" ++ go d vars a ++ " " ++ opStr ++ " " ++ go d vars b ++ ")"
        where
          opStr = case o of
            ADD -> "+";   SUB -> "-";   MUL -> "*";   DIV -> "/"
            MOD -> "%";   POW -> "**";  EQL -> "==";  NEQ -> "!=="
            LST -> "<";    GRT -> ">";   LEQ -> "<=";  GEQ -> ">="
            AND -> "&&";   OR  -> "|";   XOR -> "^"
            SHL -> "<<";   SHR -> ">>"
      Op1 o a      -> case o of
        NOT -> "(not " ++ go d vars a ++ ")"
        NEG -> "(-" ++ go d vars a ++ ")"

      -- Pair
      Sig a b      -> case cut b of
        Lam "_" _ f -> "(" ++ go (d+1) vars a ++ " & " ++ go (d+1) vars (f (Var "_" d)) ++ ")"
        Lam k _ f   -> "Σ" ++ k ++ ":" ++ go d vars a ++ ". " ++ go (d+1) vars (f (Var k d))
        _           -> "Σ" ++ go d vars a ++ ". " ++ go d vars b
      Tup _ _      -> case unsnoc (flattenTup term) of
             Just ((Sym name : xs),One) -> "@" ++ shortName name ++ "{" ++ intercalate "," (map show xs) ++ "}"
             _                          -> "(" ++ intercalate "," (map (\t -> go d vars t) (flattenTup term)) ++ ")"
      SigM f       -> "λ{(,):" ++ go d vars f ++ "}"

      -- Function
      All a b      -> case b of
        Lam "_" _ f -> go d vars a ++ " -> " ++ go (d+1) vars (f (Var "_" d))
        Lam k _ f   -> "∀" ++ k ++ ":" ++ go d vars a ++ ". " ++ go (d+1) (M.insert k d vars) (f (Var k d))
        _           -> "∀" ++ go d vars a ++ ". " ++ go d vars b
      Lam k mt f   -> case mt of
        Just t  -> "λ" ++ k ++ "^" ++ show d ++ ":" ++ go d vars t ++ ". " ++ go (d+1) vars (f (Var k d))
        Nothing -> "λ" ++ k ++  ". " ++ go (d+1) vars (f (Var k d))
      App _ _      -> fnStr ++ "(" ++ intercalate "," (map (\arg -> go d vars arg) args) ++ ")"
        where
          (fn, args) = collectApps term []
          fnStr = case cut fn of
            Var{} -> go d vars fn
            Ref{} -> go d vars fn
            _     -> "(" ++ go d vars fn ++ ")"

      -- Equality
      Eql t a b    -> typeStr ++ "{" ++ go d vars a ++ "==" ++ go d vars b ++ "}"
        where
          typeStr = case t of
            Sig _ _ -> "(" ++ go d vars t ++ ")"
            All _ _ -> "(" ++ go d vars t ++ ")"
            _       -> go d vars t
      Rfl          -> "{==}"
      EqlM f       -> "λ{{==}:" ++ go d vars f ++ "}"
      Rwt e f      -> "rewrite " ++ go d vars e ++ " " ++ go d vars f

      -- MetaVar
      Met n t ctx  -> "?" ++ n ++ ":" ++ go d vars t ++ "{" ++ intercalate "," (map (\c -> go d vars c) ctx) ++ "}"

      -- Supperpositions
      Era          -> "*"
      Sup l a b    -> "&" ++ go d vars l ++ "{" ++ go d vars a ++ "," ++ go d vars b ++ "}"
      SupM l f     -> "λ{&" ++ go d vars l ++ "{,}:" ++ go d vars f ++ "}"

      -- Errors
      Loc _ t      -> go d vars t

      -- Logging
      Log s x      -> "log " ++ go d vars s ++ " " ++ go d vars x

      -- Primitive
      Pri p        -> case p of
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

      -- Sugars
      Pat ts ms cs -> "match " ++ unwords (map (\t -> go d vars t) ts) ++ " {" ++ moves ++ cases ++ " }"
        where
          moves = case ms of
            [] -> ""
            _  -> " with " ++ intercalate " with " (map showMove ms)
          cases = case cs of
            [] -> ""
            _  -> " " ++ intercalate " " (map showCase cs)
          showMove (k,x)   = k ++ "=" ++ go d vars x
          showCase (ps,x)  = "case " ++ unwords (map showPat' ps) ++ ": " ++ go d vars x
          showPat' p       = "(" ++ go d vars p ++ ")"
      Frk l a b    -> "fork " ++ go d vars l ++ ":" ++ go d vars a ++ " else:" ++ go d vars b

shortName :: String -> String
shortName name@('0':rest) = name
shortName name@('1':rest) = case splitOn "::" rest of
  [] -> rest
  xs -> last xs
shortName name = name

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
