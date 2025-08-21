-- Bend2's Core Type
-- =================
-- This is the starting point of this repository. All other modules are files
-- from/to the core Term type. Includes Books, Errors and other helper types.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Core.Type where

import Data.Int (Int32, Int64)
import Data.List (intercalate)
import Data.Maybe (fromMaybe, fromJust)
import Data.Word (Word32, Word64)
import Debug.Trace
import qualified Data.Kind as DK
import qualified Data.Map as M
import qualified Data.Set as S

data Bits = O Bits | I Bits | E deriving Show
type Name = String
type Body = Term -> Term
type Case = ([Term], Term)
type Move = (String, Term)
type Type = Term

data NTyp
  = U64_T
  | I64_T
  | F64_T
  | CHR_T
  deriving (Show, Eq)

data NVal
  = U64_V Word64
  | I64_V Int64
  | F64_V Double
  | CHR_V Char
  deriving (Show, Eq)

data NOp2
  = ADD | SUB | MUL | DIV | MOD | POW
  | EQL | NEQ  
  | LST | GRT | LEQ | GEQ
  | AND | OR  | XOR
  | SHL | SHR
  deriving (Show, Eq)

data NOp1
  = NOT | NEG
  deriving (Show, Eq)

data PriF
  = U64_TO_CHAR
  | CHAR_TO_U64
  | HVM_INC
  | HVM_DEC
  deriving (Show, Eq)

-- Bend's Term Type
data Term
  -- Variables
  = Var Name Int -- x
  | Ref Name Int -- x, Reduce?
  | Sub Term     -- x

  -- Definitions
  | Fix Name Body                   -- μx. f
  | Let Name (Maybe Term) Term Body -- !x : T = v; f
  | Use Name Term Body              -- !x = v; f

  -- Universe
  | Set -- Set

  -- Annotation
  | Chk Term Type -- x::t
  | Tst Term      -- trust x

  -- Empty
  | Emp  -- Empty
  | EmpM -- λ{}

  -- Unit
  | Uni       -- Unit
  | One       -- ()
  | UniM Term -- λ{():f}

  -- Bool
  | Bit            -- Bool
  | Bt0            -- False
  | Bt1            -- True
  | BitM Term Term -- λ{False:t;True:t}

  -- Nat
  | Nat            -- Nat
  | Zer            -- 0
  | Suc Term       -- ↑n
  | NatM Term Term -- λ{0n:z;1n+:s}

  -- List
  | Lst Type       -- T[]
  | Nil            -- []
  | Con Term Term  -- h<>t
  | LstM Term Term -- λ{[]:n;<>:c}

  -- Enum
  | Enu [String]              -- {&foo,&bar...}
  | Sym String                -- &foo
  | EnuM [(String,Term)] Term -- λ{&foo:f;&bar:b;...d}

  -- Numbers
  | Num NTyp           -- CHR | U64 | I64 | F64
  | Val NVal           -- 123 | +123 | +123.0
  | Op2 NOp2 Term Term -- x + y
  | Op1 NOp1 Term      -- !x

  -- Pair
  | Sig Type Type -- ΣA.B
  | Tup Term Term -- (a,b)
  | SigM Term     -- λ{(,):f}

  -- Function
  | All Type Type              -- ∀A.B
  | Lam Name (Maybe Term) Body -- λx.f | λx:A.f
  | App Term Term              -- (f x)

  -- Equality
  | Eql Type Term Term -- T{a==b}
  | Rfl                -- {==}
  | EqlM Term          -- λ{{==}:f}
  | Rwt Term Term      -- rewrite e f

  -- MetaVar
  | Met Name Type [Term] -- ?N:T{x0,x1,...}

  -- Supperpositions
  | Era                 -- *
  | Sup Term Term Term  -- &L{a,b}
  | SupM Term Term      -- λ{&L{,}:f}

  -- Errors
  | Loc Span Term -- x

  -- Logging
  | Log Term Term -- log s ; x

  -- Primitive
  | Pri PriF -- SOME_FUNC

  -- Sugars
  | Pat [Term] [Move] [Case] -- match x ... { with k=v ... ; case @A ...: F ; ... }
  | Frk Term Term Term       -- fork L:a else:b

-- Book of Definitions
type Inj  = Bool -- "is injective" flag. improves pretty printing
type Defn = (Inj, Term, Type)
data Book = Book (M.Map Name Defn) [Name]

-- Substitution Map
type Subs = [(Term,Term)]

-- Context (new type)
data Ctx = Ctx [(Name,Term,Term)]

-- Error Location
data Span = Span
  { spanBeg :: (Int,Int)
  , spanEnd :: (Int,Int)
  , spanPth :: FilePath -- original file path
  , spanSrc :: String   -- source content
  } deriving (Eq, Ord)

-- Errors
data Error
  = CantInfer Span Ctx (Maybe String)
  | Unsupported Span Ctx (Maybe String)
  | Undefined Span Ctx Name (Maybe String)
  | TypeMismatch Span Ctx Term Term (Maybe String)
  | TermMismatch Span Ctx Term Term (Maybe String)
  | IncompleteMatch Span Ctx (Maybe String)
  | UnknownTermination Term
  | ImportError Span String

data Result a
  = Done a
  | Fail Error

instance Functor Result where
  fmap f (Done a) = Done (f a)
  fmap _ (Fail e) = Fail e

instance Applicative Result where
  pure              = Done
  Done f <*> Done a = Done (f a)
  Fail e <*> _      = Fail e
  _      <*> Fail e = Fail e

instance Monad Result where
  Done a >>= f = f a
  Fail e >>= _ = Fail e

-- Peano naturals at both type‑ and value‑level
data Nat = Z | S Nat

data SNat :: Nat -> DK.Type where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

-- Type‑level addition
type family Add (n :: Nat) (m :: Nat) :: Nat where
  Add Z     m = m
  Add (S n) m = S (Add n m)

-- Adds two type-level SNats
addSNat :: SNat n -> SNat m -> SNat (Add n m)
addSNat SZ     m = m
addSNat (SS n) m = SS (addSNat n m)

-- Arg<n> = n‑ary function returning Term
type family Arg (n :: Nat) :: DK.Type where
  Arg Z     = Term
  Arg (S p) = Term -> Arg p

-- LHS = pair of arity and a constructor taking exactly that many args
data LHS where
  LHS :: SNat k -> (Term -> Arg k) -> LHS

-- Utils
-- -----

getDefn :: Book -> Name -> Maybe Defn
getDefn (Book defs _) name = M.lookup name defs

cut :: Term -> Term
cut (Loc _ t) = cut t
cut (Chk x _) = cut x
cut t         = t

unlam :: Name -> Int -> (Term -> Term) -> Term
unlam k d f = f (Var k d)

collectArgs :: Term -> ([(String, Term)], Term)
collectArgs = go [] where
  go acc (Loc _ t)            = go acc t
  go acc (All t (Lam k ty f)) = go (acc ++ [(k, t)]) (f (Var k 0))
  go acc goal                 = (acc, goal)

collectApps :: Term -> [Term] -> (Term, [Term])
collectApps (cut -> App f x) args = collectApps f (x:args)
collectApps f                args = (f, args)

noSpan :: Span
noSpan = Span (0,0) (0,0) "" ""

flattenTup :: Term -> [Term]
flattenTup (Tup l r) = l : flattenTup r
flattenTup t         = [t]

isLam :: Term -> Bool
isLam (Loc _ f) = isLam f
isLam Lam{}     = True
isLam EmpM      = True
isLam UniM{}    = True
isLam BitM{}    = True
isLam NatM{}    = True
isLam LstM{}    = True
isLam EnuM{}    = True
isLam SigM{}    = True
isLam SupM{}    = True
isLam EqlM{}    = True
isLam _         = False

-- | Collects all variable usages with their names and depths
collectVars :: Term -> [(String, Int)]
collectVars t = case t of
  Var k i -> [(k, i)]
  Ref k i -> []  -- Refs don't shadow
  Sub t -> collectVars t
  Fix k f -> collectVars (f (Var k 0))
  Let k t v f -> maybe [] collectVars t ++ collectVars v ++ collectVars (f (Var k 0))
  Use k v f -> collectVars v ++ collectVars (f (Var k 0))
  Chk x t -> collectVars x ++ collectVars t
  Tst x -> collectVars x
  UniM f -> collectVars f
  BitM f t -> collectVars f ++ collectVars t
  NatM z s -> collectVars z ++ collectVars s
  Lst t -> collectVars t
  Con h t -> collectVars h ++ collectVars t
  LstM n c -> collectVars n ++ collectVars c
  EnuM cs d -> concatMap (collectVars . snd) cs ++ collectVars d
  Op2 _ a b -> collectVars a ++ collectVars b
  Op1 _ a -> collectVars a
  Sig t f -> collectVars t ++ collectVars f
  Tup a b -> collectVars a ++ collectVars b
  SigM f -> collectVars f
  All t f -> collectVars t ++ collectVars f
  Lam k t f -> maybe [] collectVars t ++ collectVars (f (Var k 0))
  App f a -> collectVars f ++ collectVars a
  Eql t a b -> collectVars t ++ collectVars a ++ collectVars b
  EqlM f -> collectVars f
  Rwt e f -> collectVars e ++ collectVars f
  Met n t ctx -> collectVars t ++ concatMap collectVars ctx
  Sup l a b -> collectVars l ++ collectVars a ++ collectVars b
  SupM l f -> collectVars l ++ collectVars f
  Loc _ t -> collectVars t
  Log s x -> collectVars s ++ collectVars x
  Pat ts ms cs -> concatMap collectVars ts ++ concatMap (collectVars . snd) ms ++ 
                  concatMap (\(ps, t) -> concatMap collectVars ps ++ collectVars t) cs
  Frk l a b -> collectVars l ++ collectVars a ++ collectVars b
  _ -> []
