{-./../Core/Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Target.Haskell where

import Control.Exception (throw)
import qualified Core.Show as Show
import Core.Type
import Core.WHNF
import Data.Char (isUpper)
import Data.List (intercalate)
import qualified Data.Map as M

-- Main compilation function
compile :: Book -> String
compile book@(Book defs _) =
  let compiledFns = map (compileDefn book) (M.toList defs)
  in prelude ++ intercalate "\n\n" compiledFns
  where
    compileDefn :: Book -> (Name, Defn) -> String
    compileDefn book (name, (_, term, typ)) = compileFn book name term typ

-- Prelude necessary for the compiled code to run
prelude :: String
prelude = unlines [
    "{-# LANGUAGE ViewPatterns #-}",
    "import Prelude (print, fromIntegral, (==), (>=), (/=), (+), (-), (*), div, mod, (^), (<), (>), (<=), negate, id, pred, Integer, Bool(..), IO, undefined, Char)",
    "import Data.Bits ((.&.), (.|.), xor, shiftL, shiftR, complement)",
    "import Data.Char (chr, ord)",
    "import Data.Int (Int64)",
    "import Data.Word (Word64)",
    "import Debug.Trace (trace)",
    "import GHC.Exts (Any)",
    "import Unsafe.Coerce (unsafeCoerce)",
    "",
    "main :: IO ()",
    "main = print (f''main)",
    ""
  ]

-- Compile a function definition
compileFn :: Book -> Name -> Term -> Term -> String
compileFn book name term typ =
  -- TODO: remove irrelevant args
  let htm = termToHT book 0 term
      hty = typeToHT book typ
      -- TODO: This is not general enough to get rid of all OTT-like equality values.
      -- E.g. if a function returns '(x, 1n+{==})' (succ applied to an equality inside of a pair), it'll still go through and become a haskell type error.
      irr = irrelevantBody hty 0
      val = case irr of { Just irr -> irr; Nothing -> htm }
      sig = refNam name ++ " :: " ++ showTerm 0 hty
      bod = refNam name ++ " =\n" ++ indent 2 ++ showTerm 2 val
  in sig ++ "\n" ++ bod
  where
    -- If the fn is irrelevant (returns ()), replace with a simple "\args. ()"
    irrelevantBody :: HT -> Int -> Maybe HT
    irrelevantBody (HAll a b) n = irrelevantBody b (n+1)
    irrelevantBody HUni       n = Just ((foldr (const $ HLam "_") HUni [1..n]))
    irrelevantBody _          n = Nothing

-- Compilation from Bend Term to Haskell Term
---------------------------------------------

-- Haskell Term ADT - simplified representation for compilation
data HT
  = HVar Name          -- Variable
  | HRef Name          -- Reference
  | HLam Name HT       -- Lambda abstraction
  | HApp HT HT         -- Function application
  | HLet Name HT HT    -- Let binding
  | HAnn HT HT         -- Annotation
  -- Type constructors
  | HAll HT HT         -- Function type
  | HAny
  | HUni               -- Unit type
  | HBit               -- Bool type
  | HNat               -- Nat type  
  | HLst HT            -- List type
  | HNum NTyp          -- Numeric type
  | HSig HT HT         -- Pair type
  | HEnu               -- Enum type
  -- Data constructors
  | HZer               -- Zero
  | HSuc HT            -- Successor
  | HNil               -- Empty list
  | HCon HT HT         -- List constructor
  | HBt1               -- True
  | HBt0               -- False
  | HOne               -- Unit value
  | HTup HT HT         -- Pair constructor
  | HSym String        -- Symbol
  -- Pattern matching
  | HMat [HT] [([HT], HT)] -- case of expression
  -- Numeric values
  | HVal NVal          -- Numeric literals
  | HOp2 NOp2 HT HT    -- Binary operations
  | HOp1 NOp1 HT       -- Unary operations
  -- Other
  | HPri PriF          -- Primitives
  | HLog HT HT         -- Log expression
  | HEra

-- Convert Bend Term to Haskell Term
termToHT :: Book -> Int -> Term -> HT
termToHT book i term = case term of
  Var n _     -> HVar n
  Ref k _     -> HRef k
  Sub t       -> termToHT book i t
  Fix n f     -> HLet n (termToHT book i (f (Var n 0))) (HVar n)
  Let k _ v f -> HLet (varNam i k) (termToHT book (i+1) v) (termToHT book (i+1) (f (Var (varNam i k) 0)))
  Use k v f   -> termToHT book i(f v)
  Set         -> HOne
  Chk v t     -> HAnn (termToHT book i v) (typeToHT book t)
  Tst v       -> termToHT book i v
  Emp         -> HOne
  EmpM        -> HLam "x''" HOne
  Uni         -> HOne
  One         -> HOne
  UniM f      -> HLam "_" (termToHT book i f)
  Bit         -> HOne
  Bt0         -> HBt0
  Bt1         -> HBt1
  BitM f t    -> HLam "x''" (HMat [HVar "x''"] [([HBt0], termToHT book i f), ([HBt1], termToHT book i t)])
  Nat         -> HOne
  Zer         -> HZer
  Suc p       -> HSuc (termToHT book i p)
  NatM z s    -> HLam "x''" (HMat [HVar "x''"] [([HZer], termToHT book i z), ([HSuc (HVar "p''")], HApp (termToHT book i s) (HVar "p''"))])
  Lst _       -> HOne
  Nil         -> HNil
  Con h t     -> HCon (termToHT book i h) (termToHT book i t)
  LstM n c    -> HLam "x''" (HMat [HVar "x''"] [([HNil], termToHT book i n), ([HCon (HVar "h''") (HVar "t''")], HApp (HApp (termToHT book i c) (HVar "h''")) (HVar "t''"))])
  Enu _       -> HEnu
  Sym s       -> HSym s
  EnuM cs d   -> HLam "x''" (HMat [HVar "x''"] ((map (\(k,f) -> ([HSym k], termToHT book i f)) cs) ++ [([HVar "x''"], HApp (termToHT book i d) (HVar "x''"))]))
  Num _       -> HOne
  Val v       -> HVal v
  Op2 o a b   -> HOp2 o (termToHT book i a) (termToHT book i b)
  Op1 o a     -> HOp1 o (termToHT book i a)
  Sig _ _     -> HOne
  Tup a b     -> HTup (termToHT book i a) (termToHT book i b)
  SigM f      -> HLam "x''" (HMat [HVar "x''"] [([HTup (HVar "a''") (HVar "b''")], HApp (HApp (termToHT book i f) (HVar "a''")) (HVar "b''"))])
  All _ _     -> HOne
  Lam n _ f   -> HLam (varNam i n) (termToHT book (i+1) (f (Var (varNam i n) 0)))
  App f x     -> HApp (termToHT book i f) (termToHT book i x)
  Eql _ _ _   -> HOne
  Rfl         -> HOne
  EqlM f      -> HLam "_" (termToHT book i f)
  Rwt _ f     -> termToHT book i f
  Met _ _ _   -> throw (Show.BendException $ CompilationError "Meta variables not supported for Haskell compilation")
  Era         -> HEra
  Sup _ _ _   -> throw (Show.BendException $ CompilationError "Superpositions not supported for Haskell compilation")
  SupM _ _    -> throw (Show.BendException $ CompilationError "Superposition matches not supported for Haskell compilation")
  Log s x     -> HLog (termToHT book i s) (termToHT book i x)
  Loc _ t     -> termToHT book i t
  Pri p       -> HPri p
  Pat xs _ cs -> HMat (map (termToHT book i) xs) (map (\(ps, b) -> (map (termToHT book i) ps, termToHT book i b)) cs)
  Frk _ _ _   -> throw (Show.BendException $ CompilationError "Fork constructs not supported for Haskell compilation")

-- Convert a Bend term to a Haskell type.
typeToHT :: Book -> Type -> HT
typeToHT book t = case whnf book t of
  Var n _     -> HVar ("t''" ++ n)
  Uni         -> HUni
  Bit         -> HBit
  Nat         -> HNat
  Lst t       -> HLst (typeToHT book t)
  Enu ss      -> HEnu
  Num t       -> HNum t
  Sig a (Lam n _ f) -> HSig (typeToHT book a) (typeToHT book (f (Var n 0)))
  All a (Lam n _ f) -> HAll (typeToHT book a) (typeToHT book (f (Var n 0)))
  Sig a b     -> HSig (typeToHT book a) (typeToHT book (whnf book (App b Emp))) 
  All a b     -> HAll (typeToHT book a) (typeToHT book (whnf book (App b Emp)))
  Set         -> HUni
  Emp         -> HUni
  Eql t a b   -> HUni
  Era         -> HAny
  _           -> HAny

-- Clean function names for Haskell
refNam :: String -> String
refNam n = "f''" ++ (map (\c -> if c == '/' then '\'' else c) n)

varNam :: Int -> String -> String
varNam i n = "x" ++ show i ++ "''" ++ n

-- Printing of Haskell Terms
----------------------------

indent :: Int -> String
indent i = replicate i ' '

-- Pretty print a Haskell value
showTerm :: Int -> HT -> String
showTerm i term = case term of
  HVar n         -> n
  HRef n         -> refNam n
  HLam n f       -> showLam i term []
  HApp f x       -> showApp i term []
  HLet n v f     -> "let " ++ n ++ " = " ++ showTerm (i+6) v ++ " in\n" ++ indent i ++ showCoerce i f
  HAnn v t       -> "(" ++ showTerm i v ++ " :: " ++ showTerm i t ++ ")"
  HAll a b       -> showAll i term []
  HAny           -> "Any"
  HUni           -> "()"
  HOne           -> "()"
  HBit           -> "Bool"
  HBt1           -> "True"
  HBt0           -> "False"
  HNat           -> "Integer"
  HZer           -> "(0 :: Integer)"
  HSuc n         -> "(" ++ showTerm i n ++ " + (1 :: Integer))"
  HLst t         -> "[" ++ showTerm i t ++ "]"
  HNil           -> "[]"
  HCon h t       -> "(" ++ showTerm i h ++ " : " ++ showTerm i t ++ ")"
  HSig a b       -> "(" ++ showTerm i a ++ ", " ++ showTerm i b ++ ")"
  HTup a b       -> "(" ++ showTerm i a ++ ", " ++ showTerm i b ++ ")"
  HEnu           -> "String"
  HSym s         -> "\"" ++ s ++ "\""
  HMat xs cs      -> "case " ++ unwords (map (showCoerce i) xs) ++ " of\n" ++ intercalate "\n" (map (showCase (i+2)) cs)
  HNum U64_T     -> "Word64"
  HNum I64_T     -> "Int64"  
  HNum F64_T     -> "Double"
  HNum CHR_T     -> "Char"
  HVal (U64_V n) -> "(" ++ show n ++ " :: Word64)"
  HVal (I64_V n) -> "(" ++ show n ++ " :: Int64)"
  HVal (F64_V n) -> "(" ++ show n ++ " :: Double)"
  HVal (CHR_V c) -> show c
  -- TODO: We need to know the type of the operands and then coerce.
  -- Since op2/op1 are polymorphic with infer on args, we can't coerce directly without manual annotations.
  HOp2 op a b    -> "(" ++ showCoerce i a ++ " " ++ showOp2 op ++ " (fromIntegral " ++ showCoerce i b ++ "))"
  HOp1 op a      -> "(" ++ showOp1 op ++ " " ++ showCoerce i a ++ ")"
  HLog s x       -> "(trace (" ++ showTerm i s ++ ") (" ++ showTerm i x ++ "))"
  HPri p         -> showPri p
  HEra           -> "undefined"

showCoerce :: Int -> HT -> String
showCoerce i t@(HLet _ _ _) = showTerm i t -- unsafeCoerce goes through let bindings for easier indentation
showCoerce i x = "(unsafeCoerce (" ++ showTerm i x ++ "))"

showApp :: Int -> HT -> [HT] -> String
showApp i (HApp f x) acc = showApp i f (x:acc)
showApp i          t acc = "(" ++ unwords (map (showCoerce i) (t:acc)) ++ ")"

showLam :: Int -> HT -> [String] -> String
showLam i (HLam n f) ks = showLam i f (n:ks)
showLam i          t ks = "(\\" ++ unwords (reverse ks) ++ " ->\n" ++ indent (i+2) ++ showCoerce (i+2) t ++ ")"

showAll :: Int -> HT -> [HT] -> String
showAll i (HAll a b) acc = showAll i b (a:acc)
showAll i          t acc = "(" ++ intercalate " -> " (map (showTerm i) (reverse (t:acc))) ++ ")"

-- Convert case pattern and body to Haskell
showCase :: Int -> ([HT], HT) -> String
showCase i (ps, f) = indent i ++ unwords (map showPat ps) ++ " ->\n" ++ indent (i+2) ++ showCoerce (i+2) f

showPat :: HT -> String
showPat pat = case pat of
  HVar n   -> n
  HTup a b -> "(" ++ showPat a ++ ", " ++ showPat b ++ ")"
  HCon h t -> "(" ++ showPat h ++ " : " ++ showPat t ++ ")"
  HNil     -> "[]"
  HZer     -> "0"
  HSuc n   -> "(pred -> " ++ showPat n ++ ")"
  HBt1     -> "True"
  HBt0     -> "False"
  HSym s   -> "\"" ++ s ++ "\""
  _ -> throw (Show.BendException $ CompilationError "Invalid pattern in Haskell compilation")

-- Convert binary operators to Haskell
showOp2 :: NOp2 -> String
showOp2 op = case op of
  ADD -> "+"
  SUB -> "-"
  MUL -> "*"
  DIV -> "`div`"
  MOD -> "`mod`"
  POW -> "^"
  EQL -> "=="
  NEQ -> "/="
  LST -> "<"
  GRT -> ">"
  LEQ -> "<="
  GEQ -> ">="
  AND -> ".&."
  OR  -> ".|."
  XOR -> "`xor`"
  SHL -> "`shiftL`"
  SHR -> "`shiftR`"

-- Convert unary operators to Haskell
showOp1 :: NOp1 -> String
showOp1 op = case op of
  NOT -> "complement"
  NEG -> "negate"

-- Convert primitives to Haskell
showPri :: PriF -> String
showPri p = case p of
  U64_TO_CHAR -> "(chr . fromIntegral)"
  CHAR_TO_U64 -> "(fromIntegral . ord)"
  HVM_INC     -> "id"
  HVM_DEC     -> "id"
