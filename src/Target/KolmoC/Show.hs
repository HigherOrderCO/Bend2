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
      -- Classify definitions
      isGen (_, KDefn _ _ (KGen _ _ _ _)) = True
      isGen _ = False
      isAssert (_, KDefn _ (Just (KEql _ _ _)) KRfl) = True
      isAssert _ = False
      isMain (n, _) = n == mainNick

      -- Partition definitions
      (mainDef, rest1) = case find isMain defs of
        Just md -> (Just md, filter (not . isMain) defs)
        Nothing -> (Nothing, defs)
      (gens, rest2) = partition isGen rest1
      (asserts, regular) = partition isAssert rest2

      -- Order: regular defs, then generators, then their asserts, then main
      allDefs = regular ++ gens ++ asserts ++ maybe [] (:[]) mainDef
  in unlines $ map showKDefn allDefs
  where
    find p [] = Nothing
    find p (x:xs) = if p x then Just x else find p xs
    partition p xs = (filter p xs, filter (not . p) xs)

-- Pretty print a single definition
showKDefn :: (Nick, KDefn) -> String
showKDefn (_, KDefn nick mtyp body) =
  -- Check if body is a generator - print as declaration, not definition
  case body of
    KGen genNick ctx typ seed ->
      "?" ++ genNick ++ showGenCtx ctx ++ " : " ++ showKCore 0 typ ++ showGenSeed seed ++ ";"
    KRfl -> case mtyp of
      -- Assert: body is Rfl and type is Eql - print as !Type{lhs==rhs};
      Just (KEql typ lhs rhs) ->
        "!" ++ showKCore 0 typ ++ "{" ++ showKCore 0 lhs ++ "==" ++ showKCore 0 rhs ++ "};"
      _ -> -- Regular definition with Rfl body
        case mtyp of
          Nothing -> "@" ++ nick ++ " = " ++ showKCore 0 body ++ " ;"
          Just typ -> "@" ++ nick ++ " : " ++ showKCore 0 typ ++ " = " ++ showKCore 0 body ++ " ;"
    -- Main reference (uppercase) - no type annotation
    KRef name | all (`elem` ['A'..'Z']) name -> "@" ++ nick ++ " = " ++ showKCore 0 body ++ " ;"
    _ -> case mtyp of
      Nothing -> "@" ++ nick ++ " = " ++ showKCore 0 body ++ " ;"
      Just typ -> "@" ++ nick ++ " : " ++ showKCore 0 typ ++ " = " ++ showKCore 0 body ++ " ;"
  where
    -- Show generator context (extract variable names from tuple list)
    showGenCtx KNil = "[]"
    showGenCtx ctx = "[" ++ intercalate ", " (extractCtxNames ctx) ++ "]"

    extractCtxNames :: KCore -> [String]
    extractCtxNames KNil = []
    extractCtxNames (KCon (KTup (KVar name) _) rest) = ("@" ++ name) : extractCtxNames rest
    extractCtxNames (KCon (KTup (KRef name) _) rest) = ("@" ++ name) : extractCtxNames rest
    extractCtxNames _ = []  -- Fallback for unexpected structure

    -- Show generator seed (omit if 0)
    showGenSeed (KUva 0) = ""
    showGenSeed (KUva n) = " #" ++ showBinary n
    showGenSeed s = " #" ++ showKCore 0 s

    showBinary n = reverse $ go n
      where
        go 0 = "0"
        go 1 = "1"
        go x = (if x `mod` 2 == 1 then '1' else '0') : go (x `div` 2)

-- Pretty print a KCore term with indentation level
showKCore :: Int -> KCore -> String
showKCore i term = case term of
  -- Variables
  KVar n       -> n
  KDP0 l n     -> n ++ "₀"  -- Using subscript 0
  KDP1 l n     -> n ++ "₁"  -- Using subscript 1

  -- Universe
  KSet         -> "*"

  -- Functions (with arrow sugar)
  KAll t b     -> showFunctionType t b
  KLam n b     -> "λ" ++ n ++ "." ++ showKCore i b
  -- Application with flattening for cleaner output
  KApp f x     ->
    let (fn, args) = flattenApp term
    in case fn of
         KRef _ -> "(" ++ showKCore i fn ++ concatMap (\a -> " " ++ showAtom i a) args ++ ")"
         _      -> "(" ++ showKCore i f ++ " " ++ showAtom i x ++ ")"

  -- Superpositions
  KEra         -> "&{}"
  KSup l a b   -> "&" ++ l ++ "{" ++ showKCore i a ++ "," ++ showKCore i b ++ "}"
  KDup l x y v b -> "!" ++ x ++ "&" ++ l ++ " = " ++ showKCore i v ++ "; " ++ showKCore i b

  -- Unit
  KUni         -> "⊤"
  KNul         -> "()"
  KUse u       -> "λ{():" ++ showKCore i u ++ "}"

  -- Booleans
  KBit         -> "𝔹"
  KBt0         -> "#0"
  KBt1         -> "#1"
  KBif f t     -> "λ{#0:" ++ showKCore i f ++ ";#1:" ++ showKCore i t ++ "}"

  -- Naturals (with numeric sugar)
  KNat         -> "ℕ"
  KZer         -> "0n"
  KSuc n       -> case natToNumber (KSuc n) of
                    Just num -> show num ++ "n"
                    Nothing  -> "1n+" ++ showAtom i n
  KInc n       -> "↑" ++ paren (showKCore i n)
  KNif z s     -> "λ{0n:" ++ showKCore i z ++ ";1n+:" ++ showKCore i s ++ "}"

  -- U32
  KU32         -> "U32"
  KUva n       -> show n
  KUif z s     -> "λ{0:" ++ showKCore i z ++ ";1+:" ++ showKCore i s ++ "}"

  -- Lists (with list sugar)
  KLst t       -> paren (showKCore i t) ++ "[]"
  KNil         -> "[]"
  KCon h t     -> case listToElements (KCon h t) of
                    Just elems -> "[" ++ intercalate "," (map (showKCore i) elems) ++ "]"
                    Nothing    -> showConsHead i h ++ " <> " ++ showConsTail i t
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

  -- Metavariables/Generators
  KGen nick ctx typ seed ->
    "?" ++ nick ++ " " ++ showKCore i ctx ++ " : " ++ showKCore i typ ++ showSeed seed
    where
      showSeed (KUva 0) = ""  -- Omit default seed
      showSeed (KUva n) = " #" ++ showBinary n
      showSeed s = " #" ++ paren (showKCore i s)

      showBinary n = reverse $ go n
        where
          go 0 = "0"
          go 1 = "1"
          go x = (if x `mod` 2 == 1 then '1' else '0') : go (x `div` 2)

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

-- Sugar helpers
-- Convert function type ∀A.λx.B to A → B
showFunctionType :: KCore -> KCore -> String
showFunctionType argType body = case body of
  KLam _ rest -> showKCore 0 argType ++ " → " ++ showKCore 0 rest
  _           -> "∀" ++ paren (showKCore 0 argType) ++ "." ++ showKCore 0 body

-- Convert natural number chains to integers
natToNumber :: KCore -> Maybe Int
natToNumber KZer = Just 0
natToNumber (KSuc n) = fmap (+1) (natToNumber n)
natToNumber _ = Nothing

-- Convert list construction to list of elements
listToElements :: KCore -> Maybe [KCore]
listToElements KNil = Just []
listToElements (KCon h t) = fmap (h:) (listToElements t)
listToElements _ = Nothing

-- Flatten application chains for cleaner printing
-- (@f a b c) instead of (((f a) b) c)
flattenApp :: KCore -> (KCore, [KCore])
flattenApp (KApp f x) =
  let (fn, args) = flattenApp f
  in (fn, args ++ [x])
flattenApp term = (term, [])

-- Show a term as an atom (wrap in parens if it's compound)
showAtom :: Int -> KCore -> String
showAtom i term = case term of
  -- Atomic terms (no parens needed)
  KVar _ -> showKCore i term
  KDP0 _ _ -> showKCore i term
  KDP1 _ _ -> showKCore i term
  KRef _ -> showKCore i term
  KBt0 -> showKCore i term
  KBt1 -> showKCore i term
  KZer -> showKCore i term
  KNul -> showKCore i term
  KRfl -> showKCore i term
  KNil -> showKCore i term
  KUva _ -> showKCore i term
  -- Terms that add their own parens
  KApp _ _ -> showKCore i term
  -- Sugar forms that are atomic
  _ | Just _ <- listToElements term -> showKCore i term
  _ | Just _ <- natToNumber term -> showKCore i term
  -- Everything else needs parens
  _ -> "(" ++ showKCore i term ++ ")"

-- Show cons head with parens for successors
showConsHead :: Int -> KCore -> String
showConsHead i h = case h of
  KSuc _ -> "(" ++ showKCore i h ++ ")"
  _      -> showAtom i h

-- Show cons tail - applications already have parens from showKCore
showConsTail :: Int -> KCore -> String
showConsTail i t = showAtom i t

-- Export main show function
showKolmoC :: KBook -> Nick -> String
showKolmoC = showKBook