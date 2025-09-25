{-# LANGUAGE ViewPatterns #-}

module Target.KolmoC where

import Data.Word (Word32)
import qualified Data.Map as M
import qualified Core.Show as Show
import Core.Type
import Core.WHNF


type Nick  = String
type Lab  = Word32

-- Extract a label from a Term, error if not convertible
getLabel :: Term -> Lab
getLabel term = case term of
  Val (U64_V v) -> fromIntegral v
  _             -> error "getLabel: expected numeric value for label"

-- KolmoC Term ADT
data KT
  -- variables
  = KVar Nick    -- Variable reference
  | KDP0 Nick    -- Duplication pair left component "Nick₀"
  | KDP1 Nick    -- Duplication pair right component "Nick₁"
  -- universe
  | KSet         -- Universe type "*"
  -- lambdas
  | KAll KT KT   -- Universal quantification "∀ Term . Term"
  | KLam Nick KT -- Lambda abstraction "λ Nick . Term"
  | KApp KT KT   -- (f x)
  -- superpositions
  | KEra         -- Erasure "&{}"
  | KSup Lab KT KT -- Superposition "&Label{Term,Term}"
  -- empty
  | KEmp         -- Bottom type "⊥"
  | KErf         -- empty match λ{}
  -- unit
  | KUni         -- Unit type "⊤"
  | KNul         -- Unit value "()"
  | KUse KT      -- Unit eliminator "λ{():Term;}"
  -- booleans
  | KBit         -- Boolean type "𝔹"
  | KBt0         -- Boolean false "#0"
  | KBt1         -- Boolean true "#1"
  | KBif KT KT   -- Boolean eliminator "λ{#0:Term;#1:Term;}"
  -- naturals
  | KNat         -- Natural number type "ℕ"
  | KZer         -- Zero "0n"
  | KSuc KT      -- Successor "1n+Term"
  | KInc KT      -- Increment "↑Term"
  | KNif KT KT   -- Natural eliminator "λ{0n:Term;1n+:Term;}"
  -- unsigned 32 bit integers
  | KU32         -- 32-bit unsigned integer type "U32"
  | KUVA         -- Unsigned integer value (Decimal|Hex|Bin)
  | KUif KT KT   -- Unsigned integer eliminator "λ{0:Term;1+:Term;}"
  -- lists
  | KLst KT      -- List type "Term[]"
  | KNil         -- List NIL
  | KCon KT KT   -- List cons "Term<>Term"
  | KMat KT KT   -- List match "λ{[]:Term;<>:Term;}"
  -- equality
  | KEql KT KT KT -- Equality type "Term{Term==Term}"
  | KRfl         -- Reflexivity proof "{==}"
  | KEif KT      -- Equality eliminator "λ{{==}:Term;}"
  -- pairs
  | KSig KT KT   -- Dependent pair type "Σ Term . Term"
  | KTup KT KT   -- Pair value "#(Term,Term)"
  | KGet KT      -- Pair eliminator "λ{#(,):Term;}"
  -- dups
  | KDup Nick Lab KT KT  -- Duplication "! Nick &Label = initializer ; continuation"
  -- function
  | KRef Nick    -- Function reference "@Nick"
  deriving Show
  

termToKT :: Book -> Int -> Term -> KT
termToKT book i term = case term of
  Var n _       -> KVar n
  Ref k _       -> KRef k
  Sub t         -> termToKT book i t
  Fix n f       -> error "TODO: Fix not supported"
  Let k _ v f   -> do
    let b = termToKT book i (f (Var k 0))
    let a = termToKT book i v
    KApp (KLam k b) a 
  Use k v f     -> termToKT book i (f v)
  Set           -> KSet
  Chk v t       -> termToKT book i v
  Tst v         -> termToKT book i v
  Emp           -> KEmp
  EmpM          -> KErf
  Uni           -> KUni
  One           -> KNul
  UniM t        -> KUse (termToKT book i t)
  Bit           -> KBit
  Bt0           -> KBt0
  Bt1           -> KBt1
  BitM f t      -> KBif (termToKT book i f) (termToKT book i t)
  Nat           -> KNat
  Zer           -> KZer
  Suc p         -> KSuc (termToKT book i p)
  NatM z s      -> KNif (termToKT book i z) (termToKT book i s)
  Lst t         -> KLst (termToKT book i t)
  Nil           -> KNil
  Con h t       -> KCon (termToKT book i h) (termToKT book i t)
  LstM n c      -> KMat (termToKT book i n) (termToKT book i c)
  Enu _         -> error "TODO: Enu (enum) not supported"
  Sym s         -> error "TODO: Sym (symbol) not supported"
  EnuM _ _      -> error "TODO: EnuM (enum match) not supported"
  Num U64_T     -> KU32  -- mapping U64 to U32 target
  Num I64_T     -> error "TODO: I64_T not supported"
  Num F64_T     -> error "TODO: F64_T not supported"
  Num CHR_T     -> error "TODO: CHR_T not supported"
  Val (U64_V v) -> KUVA
  Val (I64_V _) -> error "TODO: I64_V not supported"
  Val (F64_V _) -> error "TODO: F64_V not supported"
  Val (CHR_V _) -> error "TODO: CHR_V not supported"
  Op2 o a b     -> error "TODO: Op2 not supported"
  Op1 o a       -> error "TODO: Op1 not supported"
  Sig a b       -> KSig (termToKT book i a) (termToKT book i b)
  Tup a b       -> KTup (termToKT book i a) (termToKT book i b)
  SigM f        -> KGet (termToKT book i f)
  All a b       -> KAll (termToKT book i a) (termToKT book i b)
  Lam n _ f     -> KLam n (termToKT book (i+1) (f (Var n 0)))
  App f x       -> KApp (termToKT book i f) (termToKT book i x)
  Eql t a b     -> KEql (termToKT book i t) (termToKT book i a) (termToKT book i b)
  Rfl           -> KRfl
  EqlM f        -> KEif (termToKT book i f)
  Rwt e f       -> error "TODO: Rwt (rewrite) not supported"
  Met _ _ _     -> error "TODO: Met (meta variables) not supported"
  Era           -> KEra
  Sup l a b     -> KSup (getLabel l) (termToKT book i a) (termToKT book i b)
  SupM l f     -> do
    let label = getLabel l
    let continuation = termToKT book i f
    let nick = "dup" ++ show i  -- generate fresh nick based on current depth
    let arg = KVar "x"  -- the argument that will be passed to this lambda
    KLam "x" (KDup nick label arg continuation)
  Log s x       -> error "TODO: Log not supported"
  Loc _ t       -> termToKT book i t 
  Pri p         -> error "TODO: Pri (primitives) not supported"
  Pat xs _ cs   -> error "TODO: Pat (pattern match) not supported"
  Frk _ _ _     -> error "TODO: Frk (fork) not supported"
  IO _          -> error "TODO: IO not supported"

-- Convert a Bend type to a KolmoC type
typeToKT :: Book -> Type -> KT
typeToKT book t = case whnf book t of
  Var n _       -> KVar ("t''" ++ n)
  Uni           -> KUni
  Bit           -> KBit
  Nat           -> KNat
  Lst t         -> KLst (typeToKT book t)
  IO t          -> error "TODO: IO type not supported in KolmoC"
  Enu _         -> error "TODO: Enu type not supported in KolmoC"
  Num U64_T     -> KU32  -- mapping U64 to U32 target
  Num I64_T     -> error "TODO: I64_T type not supported"
  Num F64_T     -> error "TODO: F64_T type not supported"
  Num CHR_T     -> error "TODO: CHR_T type not supported"
  Sig a (Lam n _ f) -> KSig (typeToKT book a) (typeToKT book (f (Var n 0)))
  All a (Lam n _ f) -> KAll (typeToKT book a) (typeToKT book (f (Var n 0)))
  Sig a b       -> KSig (typeToKT book a) (typeToKT book (whnf book (App b Emp)))
  All a b       -> KAll (typeToKT book a) (typeToKT book (whnf book (App b Emp)))
  Set           -> KSet
  Emp           -> KEmp
  Eql t a b     -> KEql (typeToKT book t) (typeToKT book a) (typeToKT book b)
  Era           -> KEra
  _             -> error "TODO: unsupported type in typeToKT"

-- Printing of KolmoC Terms
----------------------------

indent :: Int -> String
indent i = replicate i ' '

-- Pretty print a KolmoC term
showKT :: Int -> KT -> String
showKT i term = case term of
  KVar n         -> n
  KRef n         -> "@" ++ n
  KDP0 n         -> n ++ "₀"
  KDP1 n         -> n ++ "₁"
  KLam n f       -> showLam i term []
  KApp f x       -> showApp i term []
  KAll a b       -> showAll i term []
  KSet           -> "*"
  KEra           -> "&{}"
  KSup l a b     -> "&" ++ show l ++ "{" ++ showKT i a ++ "," ++ showKT i b ++ "}"
  KEmp           -> "⊥"
  KErf           -> "λ{}"
  KUni           -> "⊤"
  KNul           -> "()"
  KUse f         -> "λ{():" ++ showKT i f ++ ";}"
  KBit           -> "𝔹"
  KBt0           -> "#0"
  KBt1           -> "#1"
  KBif f t       -> "λ{#0:" ++ showKT i f ++ ";#1:" ++ showKT i t ++ ";}"
  KNat           -> "ℕ"
  KZer           -> "0n"
  KSuc n         -> "1n+" ++ showKT i n
  KInc n         -> "↑" ++ showKT i n
  KNif z s       -> "λ{0n:" ++ showKT i z ++ ";1n+:" ++ showKT i s ++ ";}"
  KU32           -> "U32"
  KUVA           -> "42"  -- placeholder for now
  KUif z s       -> "λ{0:" ++ showKT i z ++ ";1+:" ++ showKT i s ++ ";}"
  KLst t         -> showKT i t ++ "[]"
  KNil           -> "[]"
  KCon h t       -> showKT i h ++ "<>" ++ showKT i t
  KMat n c       -> "λ{[]:" ++ showKT i n ++ ";<>:" ++ showKT i c ++ ";}"
  KEql t a b     -> showKT i t ++ "{" ++ showKT i a ++ "==" ++ showKT i b ++ "}"
  KRfl           -> "{==}"
  KEif f         -> "λ{{==}:" ++ showKT i f ++ ";}"
  KSig a b       -> "Σ" ++ showKT i a ++ "." ++ showKT i b
  KTup a b       -> "#(" ++ showKT i a ++ "," ++ showKT i b ++ ")"
  KGet f         -> "λ{#(,):" ++ showKT i f ++ ";}"
  KDup n l init cont -> "!" ++ n ++ "&" ++ show l ++ "=" ++ showKT i init ++ ";" ++ showKT i cont

showApp :: Int -> KT -> [KT] -> String
showApp i (KApp f x) acc = showApp i f (x:acc)
showApp i          t acc = "(" ++ unwords (map (showKT i) (t:acc)) ++ ")"

showLam :: Int -> KT -> [String] -> String
showLam i (KLam n f) ks = showLam i f (n:ks)
showLam i          t ks = "λ" ++ unwords (reverse ks) ++ "." ++ showKT i t

showAll :: Int -> KT -> [KT] -> String
showAll i (KAll a b) acc = showAll i b (a:acc)
showAll i          t acc = "∀" ++ unwords (map (showKT i) (reverse acc)) ++ "." ++ showKT i t

-- Main compilation function
compile :: Book -> String
compile book@(Book defs _) =
  let compiledFns = map (compileDefn book) (M.toList defs)
  in unlines compiledFns
  where
    compileDefn :: Book -> (Name, Defn) -> String
    compileDefn book (name, (_, term, typ)) = compileFn book name term typ

-- Compile a function definition
compileFn :: Book -> Name -> Term -> Term -> String
compileFn book name term typ =
  let ktm = termToKT book 0 term
      kty = typeToKT book typ
      sig = "@" ++ name ++ " : " ++ showKT 0 kty ++ " ;"
      bod = "@" ++ name ++ " = " ++ showKT 0 ktm ++ " ;"
  in sig ++ "\n" ++ bod




