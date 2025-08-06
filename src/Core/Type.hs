-- REFACTOR SPEC:
-- We're now refactoring Bend2 to include a proper Algebraic Datatype system.
-- Previously, we emulated algebraic datatypes with enums and sigmas. For ex:
-- type Vec<A: Set, N: Nat>:
--   case @Nil:
--     e: Nat{N == 0n}
--   case @Con:
--     n: Nat
--     h: A
--     t: Vec(A,n)
--     e: Nat{N == (1n+n)}
-- Desugared to:
-- Vec : ∀A:Set. ∀N:Nat. Set =
--   λA:Set. λN:Nat.
--     Σenum{&Nil,&Con}.
--     λ{
--       &Nil: Σe:Nat{N==0n}. Unit
--       &Con: Σn:Nat. Σh:A. Σt:Vec(A,n). Σe:Nat{N==1n+n}. Unit
--       λ_. ()
--     }
-- To pattern-match an ADT, the user had to write
-- match vec:
--   case (&Nil, fs):
--     ...
--   case (&Con, fs):
--     match fs:
--       case (n, fs):
--         match fs:
--           case (h, fs):
--             match fs:
--               case (t, fs):
--                 match e:
--                   case (e, fs):
--                     ...
-- Which was verbose and error-prone.
-- This change will remove enums, and introduce proper ADTs.
-- Previously, constructors were written as:
-- - `@Foo{v0,v1,...}` -- without names
-- And they desugared to:
-- - `(&Foo,v0,v1,...,())`
-- Where &Foo was an enum symbol.
-- Now, constructors will be written as:
-- - `Foo{v0,v1,...}`
-- And will not be desugared - there is a native variant for it (Ctr). Note
-- that, to distinguish constructors from variables, we need the ending '{}'.
-- That is, `Nil` is a variable, and `Nil{}` is a constructor. Also, to avoid
-- conflict, the old equality syntax changes from `T{a == b}` to `a == b :: T`.
-- We also include a new λ-match for ADTs:
-- - `λT{ Ctr{}: ctr_case ; ... ; {}: def_case }`
-- Where:
-- - `T` is the name of the eliminated ADT.
-- - `K{}: K_case` is the case for the K constructor.
-- - `{}: case` is a default case.
-- As a syntax-sugar, the user can write cases like:
-- - `λT{ ... Ctr{x0,x1,...}: ctr_case ... }`
-- Which desugars to:
-- - `λ{ ... Ctr{}: λx0. λx1. ctr_case ... }`
-- And they can write default cases like:
-- - `λ{ ... x: def_case }`
-- Which desugars to:
-- - `λ{ ... {}: λx. def_case }`
-- I.e., the parser introduces the lambdas for convenience.
-- We also include a variant to refer to an ADT:
-- - `type T<p0,p1,...>`
-- Which denotes the ADT `T` parametrized with `p0, p1...`.
-- Finally, the following top-level syntax declares a new ADT:
-- type Vec<A: Set, N: Nat>:
--   case Nil{}:
--     e: N == 0n :: Nat
--   case Con{}:
--     n: Nat
--     h: A
--     t: type Vec<A,n>
--     e: N == 1n+n :: Nat
-- Syntactically, only change is how constructors/types/equality are written.
-- Semantically, when a top-level ADT is parsed, instead of desugaring it to a
-- top-level definition with sigmas and enums, we just register it in the book,
-- which now includes a map of top-level ADTs. For Vec, we register:
-- DataType "Vec" type ctrs
-- Where:
-- type ::= ∀ A:Set N:Nat . Set
-- ctrs["Nil"] ::= λp. ∀ e:(N == 0n : Nat) . p(Nil{x})
-- ctrs["Con"] ::= λp. ∀ n:Nat h:A t:(type Vec<A,n>) e:(N == 1n+n : Nat) . p(Con{n,h,t,e})
-- Notice how we built the constructors types to simplify type-checking.

-- For convenience, we also add the following top-level function:
-- def Vec : ∀A: set. ∀N: Nat. Set = type Vec<A, N>
-- This allows `Vec<A,N>` (internally, a Ref applied to arguments) to reduce to
-- `@Vec<A,N>` (internally, an ADT reference).
-- 
-- Notes:
-- 
-- The expression
-- (λ{ Con{}: F ; Nil{}: G } Con{1n,h,t,e})
-- reduces to:
-- F(1n,h,t,e)
-- Because the scrutinee name, Con, is in the case list.
--
-- The expression:
-- (λ{ Nil{}: G ; {}: D } Con{1n,h,t,e})
-- Reduces to:
-- D(Con{1n,h,t,e})
-- Because the scrutinee name, Con, is not in the case list, and there is a
-- default case. Notice the default case is applied to the entire term!
--
-- The expression:
-- (λ{ Nil{}: G ; {}: D } 123)
-- Doesn't reduce, because 123 isn't a constructor (stuck form).
-- 
-- As for type-checking, to check:
-- check λ{ Con{}: F ; Nil: G } :: ∀x:(type Vec<A,N>) . P(x)
-- We:
-- - Retrieve 'Vec' from the ADT Map on the Book.
-- - check F : ∀ n:Nat h:A t:Vec<A,n> e:(N == 1n+n : Nat) . P(Con{n,h,t,e})
-- - check G : ∀ e:(N == 0n : Nat) . P(Nil{e})
-- Notice we get the case types by applying the return type of the All to the
-- type stored in the given constructor entry of the retrieved ADT.
-- We don't implement datatype indices. Fording is used to emulate them.

-- Keep your code simple and idiomatic.
--
-- GOAL: refactor the codebase to implement the changes above.
-- When I give you a commented-out code, REWRITE IT FULLY.
-- Do NOT remove any old feature, behavior, quirk, comment.

-- Bend2's Core Type
-- =================
-- This is the starting point of this repository. All other modules are files
-- from/to the core Term type. Includes Books, Errors and other helper types.

{-# LANGUAGE DataKinds #-}
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

  -- REMOVED
  -- -- Enum
  -- | Enu [String]              -- {&foo,&bar...}
  -- | Sym String                -- &foo
  -- | EnuM [(String,Term)] Term -- λ{&foo:f;&bar:b;...d}

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
  | Eql Type Term Term -- a==b:T
  | Rfl                -- {==}
  | EqlM Term          -- λ{{==}:f}
  | Rwt Term Term      -- rewrite e f

  -- ADTs (NEW)
  | ADT  Name [Term]                     -- type T<p0,p1,...>
  | Ctr  Name [Term]                     -- K{v0,v1,...}
  | ADTM Name [(Name,Term)] (Maybe Term) -- λT{ K{}: K_case ; ... ; {}: def_case }

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
  | Pat [Term] [Move] [Case] -- match x ... { with k=v ... ; case A{} ...: F ; ... }
  | Frk Term Term Term       -- fork L:a else:b

-- Book of Definitions

-- REMOVED:
-- type Inj  = Bool -- "is injective" flag
-- type Defn = (Inj, Term, Type)
-- NOTE: The 'Inj' flag was only needed to pretty print ADTs encoded with
-- Sigmas. With native ADTs, we don't need it anymore, so it was removed.

type DataCtr
  = (Name, Type -> Type) -- ("K" , λP. ∀ x0:T0 x1:T1 ... P(@K{x0,x1,...}))

data DataType
  = DataType
  { adtName :: Name      -- Name
  , adtType :: Type      -- Type
  , adtCtrs :: [DataCtr] -- Constructors
  }

data Function
  = Function
  { funName :: Name
  , funType :: Type
  , funBody :: Term
  }

data Book
  = Book
  { bookFun :: M.Map Name Function -- global functions
  , bookADT :: M.Map Name DataType -- global datatypes
  , bookNam :: [Name]              -- order of definition
  }

-- Context
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
  = CantInfer Span Ctx
  | Unsupported Span Ctx
  | Undefined Span Ctx Name
  | TypeMismatch Span Ctx Term Term
  | TermMismatch Span Ctx Term Term
  | IncompleteMatch Span Ctx
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

-- Arg<n> = n‑ary function returning Term
type family Arg (n :: Nat) :: DK.Type where
  Arg Z     = Term
  Arg (S p) = Term -> Arg p

-- LHS = pair of arity and a constructor taking exactly that many args
data LHS where
  LHS :: SNat k -> (Term -> Arg k) -> LHS

-- Utils
-- -----

-- Adds two type-level SNats
addSNat :: SNat n -> SNat m -> SNat (Add n m)
addSNat SZ     m = m
addSNat (SS n) m = SS (addSNat n m)

getFun :: Book -> Name -> Maybe Function
getFun (Book funs _ _) name = M.lookup name funs

getADT :: Book -> Name -> Maybe DataType
getADT (Book _ adts _) name = M.lookup name adts

cut :: Term -> Term
cut (Loc _ t) = cut t
cut (Chk x _) = cut x
cut t         = t

unlam :: Name -> Int -> (Term -> Term) -> Term
unlam k d f = f (Var k d)

collectApps :: Term -> [Term] -> (Term, [Term])
collectApps (cut -> App f x) args = collectApps f (x:args)
collectApps f                args = (f, args)

noSpan :: Span
noSpan = Span (0,0) (0,0) "" ""

isLam :: Term -> Bool
isLam (Loc _ f) = isLam f
isLam Lam{}     = True
isLam EmpM      = True
isLam UniM{}    = True
isLam BitM{}    = True
isLam NatM{}    = True
isLam LstM{}    = True
-- isLam EnuM{}    = True -- REMOVED
isLam ADTM{}    = True -- NEW
isLam SigM{}    = True
isLam SupM{}    = True
isLam EqlM{}    = True
isLam _         = False

-- Convenience function: getCtrADT -- given a ctr name, returns its DatType
getCtrADT :: Book -> Name -> Maybe DataType
getCtrADT (Book _ adts _) ctrName = 
  case filter sameName (M.elems adts) of
    [adt] -> Just adt
    _     -> Nothing
  where sameName adt = any (\ (name, _) -> name == ctrName) (adtCtrs adt)

-- Convenience function: getCtr -- given a ctr name, returns its DataCtr
getCtr :: Book -> Name -> Maybe DataCtr
getCtr book ctrName = do
  adt <- getCtrADT book ctrName
  case filter (\(name, _) -> name == ctrName) (adtCtrs adt) of
    [ctr] -> Just ctr
    _     -> Nothing

getAdtName :: Book -> Case -> Name
getAdtName book ([(cut -> Ctr cname _)], _) = 
  case getCtrADT book cname of
    Just adt -> adtName adt
    Nothing  -> error $ "Constructor " ++ cname ++ " not found in book"
getAdtName _ _ = error "Invalid ADT pattern"
