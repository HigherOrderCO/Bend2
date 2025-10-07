module Target.KolmoC.Show where

import Data.List (intercalate)
import Data.Word (Word32)
import qualified Data.Map as M
import Numeric (showHex)

import Target.KolmoC.Type

-- Pretty print a KolmoC book with all definitions
showKBook :: KBook -> Nick -> String
showKBook kbook mainNick =
  let defs = M.toList kbook
      -- Put main last if it exists
      (mainDef, otherDefs) = case find (\(n,_) -> n == mainNick) defs of
        Just md -> (Just md, filter (\(n,_) -> n /= mainNick) defs)
        Nothing -> (Nothing, defs)
      allDefs = otherDefs ++ maybe [] (:[]) mainDef
  in unlines $ map showKDefn allDefs
  where
    find p [] = Nothing
    find p (x:xs) = if p x then Just x else find p xs

-- Pretty print a single definition
showKDefn :: (Nick, KDefn) -> String
showKDefn (_, KDefn nick mtyp body) =
  case mtyp of
    Nothing -> "@" ++ nick ++ " = " ++ showKCore 0 body ++ " ;"
    Just typ -> "@" ++ nick ++ " : " ++ showKCore 0 typ ++ " = " ++ showKCore 0 body ++ " ;"

-- Pretty print a KCore term with indentation level
showKCore :: Int -> KCore -> String
showKCore i term = case term of
  -- Variables
  KVar n       -> n
  KDP0 l n     -> n ++ "₀"  -- Using subscript 0
  KDP1 l n     -> n ++ "₁"  -- Using subscript 1

  -- Universe
  KSet         -> "*"

  -- Functions
  KAll t b     -> "∀" ++ paren (showKCore i t) ++ "." ++ showKCore i b
  KLam n b     -> "λ" ++ n ++ "." ++ showKCore i b
  KApp f x     -> "(" ++ showKCore i f ++ " " ++ showKCore i x ++ ")"

  -- Superpositions
  KEra         -> "&{}"
  KSup l a b   -> "&" ++ l ++ "{" ++ showKCore i a ++ "," ++ showKCore i b ++ "}"
  KDup l x y v b -> "!" ++ x ++ "&" ++ l ++ "=" ++ showKCore i v ++ "; " ++ showKCore i b

  -- Unit
  KUni         -> "⊤"
  KNul         -> "()"
  KUse u       -> "λ{():" ++ showKCore i u ++ "}"

  -- Booleans
  KBit         -> "𝔹"
  KBt0         -> "#0"
  KBt1         -> "#1"
  KBif f t     -> "λ{#0:" ++ showKCore i f ++ ";#1:" ++ showKCore i t ++ "}"

  -- Naturals
  KNat         -> "ℕ"
  KZer         -> "0n"
  KSuc n       -> "1n+" ++ paren (showKCore i n)
  KInc n       -> "↑" ++ paren (showKCore i n)
  KNif z s     -> "λ{0n:" ++ showKCore i z ++ ";1n+:" ++ showKCore i s ++ "}"

  -- U32
  KU32         -> "U32"
  KUva n       -> show n
  KUif z s     -> "λ{0:" ++ showKCore i z ++ ";1+:" ++ showKCore i s ++ "}"

  -- Lists
  KLst t       -> paren (showKCore i t) ++ "[]"
  KNil         -> "[]"
  KCon h t     -> showKCore i h ++ " <> (" ++ showKCore i t ++ ")"
  KMat n c     -> "λ{[]:" ++ showKCore i n ++ ";<>:" ++ showKCore i c ++ "}"

  -- Equality
  KEql t a b   -> paren (showKCore i t) ++ "{" ++ showKCore i a ++ "==" ++ showKCore i b ++ "}"
  KRfl         -> "{==}"
  KRwt e p f   -> "~" ++ paren (showKCore i e) ++ ":" ++ paren (showKCore i p) ++ ";" ++ showKCore i f

  -- Pairs
  KSig t f     -> "Σ" ++ paren (showKCore i t) ++ "." ++ showKCore i f
  KTup a b     -> "#(" ++ showKCore i a ++ "," ++ showKCore i b ++ ")"
  KGet p       -> "λ{#(,):" ++ showKCore i p ++ "}"

  -- References
  KRef n       -> "@" ++ n
  KTyp n       -> "@:" ++ n

  -- Empty
  KEmp         -> "⊥"
  KErf         -> "λ{}"

  -- Spinners
  KSpn n x     -> "&" ++ n ++ "(" ++ showKCore i x ++ ")"

  -- Primitives (custom handling for special operations)
  KPri op args -> showPrimitive op args i

-- Helper to add parentheses when needed
paren :: String -> String
paren s = if needsParen s then "(" ++ s ++ ")" else s
  where
    needsParen s = ' ' `elem` s || any (`elem` s) "λ∀Σ"

-- Show primitive operations
showPrimitive :: String -> [KCore] -> Int -> String
showPrimitive op args i = case (op, args) of
  -- Binary operations
  ("ADD", [a, b]) -> "(" ++ showKCore i a ++ " + " ++ showKCore i b ++ ")"
  ("SUB", [a, b]) -> "(" ++ showKCore i a ++ " - " ++ showKCore i b ++ ")"
  ("MUL", [a, b]) -> "(" ++ showKCore i a ++ " * " ++ showKCore i b ++ ")"
  ("DIV", [a, b]) -> "(" ++ showKCore i a ++ " / " ++ showKCore i b ++ ")"
  ("MOD", [a, b]) -> "(" ++ showKCore i a ++ " % " ++ showKCore i b ++ ")"
  ("EQ",  [a, b]) -> "(" ++ showKCore i a ++ " == " ++ showKCore i b ++ ")"
  ("NEQ", [a, b]) -> "(" ++ showKCore i a ++ " != " ++ showKCore i b ++ ")"
  ("LT",  [a, b]) -> "(" ++ showKCore i a ++ " < " ++ showKCore i b ++ ")"
  ("GT",  [a, b]) -> "(" ++ showKCore i a ++ " > " ++ showKCore i b ++ ")"
  ("LEQ", [a, b]) -> "(" ++ showKCore i a ++ " <= " ++ showKCore i b ++ ")"
  ("GEQ", [a, b]) -> "(" ++ showKCore i a ++ " >= " ++ showKCore i b ++ ")"
  ("AND", [a, b]) -> "(" ++ showKCore i a ++ " & " ++ showKCore i b ++ ")"
  ("OR",  [a, b]) -> "(" ++ showKCore i a ++ " | " ++ showKCore i b ++ ")"
  ("XOR", [a, b]) -> "(" ++ showKCore i a ++ " ^ " ++ showKCore i b ++ ")"
  ("SHL", [a, b]) -> "(" ++ showKCore i a ++ " << " ++ showKCore i b ++ ")"
  ("SHR", [a, b]) -> "(" ++ showKCore i a ++ " >> " ++ showKCore i b ++ ")"

  -- Unary operations
  ("NOT", [a])    -> "(!" ++ showKCore i a ++ ")"
  ("NEG", [a])    -> "(-" ++ showKCore i a ++ ")"
  ("INC", [a])    -> "↑" ++ paren (showKCore i a)
  ("DEC", [a])    -> "↓" ++ paren (showKCore i a)

  -- Special primitives
  ("U64_TO_CHAR", [a]) -> "/u64_to_char(" ++ showKCore i a ++ ")"
  ("CHAR_TO_U64", [a]) -> "/char_to_u64(" ++ showKCore i a ++ ")"

  -- Symbols (enum constructors)
  (op, []) | take 4 op == "SYM:" -> "'" ++ drop 4 op ++ "'"

  -- Default: show as primitive call
  _ -> "/" ++ op ++ if null args
                     then ""
                     else "(" ++ intercalate "," (map (showKCore i) args) ++ ")"

-- Export main show function
showKolmoC :: KBook -> Nick -> String
showKolmoC = showKBook