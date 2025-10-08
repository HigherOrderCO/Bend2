{-# LANGUAGE DeriveGeneric #-}

module Target.KolmoC.Type where

import Data.Word (Word32)
import qualified Data.Map as M
import qualified Data.Set as S
import GHC.Generics (Generic)
import Core.Type (Term, Book, NOp2(..), NVal(..), PriF(..))

-- Type aliases for clarity
type Name = String
type Lab = String  -- 4-letter label for superpositions/dups
type Nick = String -- 4-letter nick for definitions

-- KolmoC Core AST
-- Represents the core term structure of KolmoC
data KCore
  -- Variables
  = KVar Name           -- x (variable reference)
  | KDP0 Lab Name       -- x₀ (left dup reference)
  | KDP1 Lab Name       -- x₁ (right dup reference)

  -- Universe
  | KSet                -- * (type universe)

  -- Functions
  | KAll KCore KCore    -- ∀A.B (dependent function type)
  | KLam Name KCore     -- λx.f (lambda abstraction)
  | KApp KCore KCore    -- (f x) (application)

  -- Superpositions
  | KEra                -- &{} (eraser)
  | KSup Lab KCore KCore -- &L{x,y} (superposition)
  | KDup Lab Name Name KCore KCore -- !x&L=v; body (duplication/sharing)

  -- Unit
  | KUni                -- ⊤ (unit type)
  | KNul                -- () (unit value)
  | KUse KCore          -- λ{():u} (unit eliminator)

  -- Booleans
  | KBit                -- 𝔹 (bool type)
  | KBt0                -- #0 (false)
  | KBt1                -- #1 (true)
  | KBif KCore KCore    -- λ{#0:f;#1:t} (bool eliminator)

  -- Naturals
  | KNat                -- ℕ (nat type)
  | KZer                -- 0n (zero)
  | KSuc KCore          -- 1n+x (successor)
  | KInc KCore          -- ↑x (increment operator)
  | KNif KCore KCore    -- λ{0n:z;1n+:s} (nat eliminator)

  -- Unsigned 32-bit integers
  | KU32                -- U32 (u32 type)
  | KUva Word32         -- numeric value (unboxed u32)
  | KUif KCore KCore    -- λ{0:z;1+:s} (u32 eliminator)

  -- Lists
  | KLst KCore          -- T[] (list type)
  | KNil                -- [] (empty list)
  | KCon KCore KCore    -- x<>y (cons)
  | KMat KCore KCore    -- λ{[]:n;<>:c} (list eliminator)

  -- Equality
  | KEql KCore KCore KCore -- T{a==b} (equality type)
  | KRfl                -- {==} (reflexivity)
  | KRwt KCore KCore KCore -- ~e:P;f (rewrite)

  -- Pairs
  | KSig KCore KCore    -- Σx.y (dependent pair type)
  | KTup KCore KCore    -- #(x,y) (pair value)
  | KGet KCore          -- λ{#(,):p} (pair eliminator)

  -- References
  | KRef Nick           -- @F (function reference)
  | KTyp Nick           -- @:F (type reference)

  -- Empty (bottom)
  | KEmp                -- ⊥ (empty type)
  | KErf                -- λ{} (empty match/absurdity)

  -- Special spinners (for call-by-name references)
  | KSpn Nick KCore     -- &fn(xs) (spinner for refs with args)

  -- Primitives (for operations that don't map directly)
  | KPri String [KCore] -- Primitive operations with args

  -- Metavariables/Generators
  | KGen Nick KCore KCore KCore -- ?N ctx : typ #seed (program generator)
  deriving (Show, Eq, Generic)

-- Binary operations that KolmoC supports
data KOp2
  = K_ADD | K_SUB | K_MUL | K_DIV | K_MOD
  | K_EQ  | K_NEQ | K_LT  | K_GT  | K_LEQ | K_GEQ
  | K_AND | K_OR  | K_XOR | K_SHL | K_SHR
  deriving (Show, Eq)

-- A compiled definition
data KDefn = KDefn
  { kdefName :: Nick          -- Definition name (4-letter nick)
  , kdefType :: Maybe KCore    -- Optional type annotation
  , kdefBody :: KCore          -- Definition body
  } deriving (Show, Eq)

-- A book of compiled definitions
type KBook = M.Map Nick KDefn

-- Compilation errors
data KCompileError
  = UnsupportedConstruct String
  | UnsupportedNumericType String
  | PatternMatchNotDesugared String
  | IONotSupported String
  | MetaVariableNotSupported String
  | ForkNotSupported String
  | NumericConversionWarning String Word32
  | InvalidNick String
  | UnknownReference String
  | DuplicateDefinition Nick
  deriving (Show, Eq)

-- Result type for compilation
type KResult a = Either KCompileError a

-- Helper to track compilation context
data CompileCtx = CompileCtx
  { ctxBook :: Book           -- Original Bend book
  , ctxDefs :: KBook          -- Accumulated KolmoC definitions
  , ctxFresh :: Int           -- Fresh name counter
  , ctxWarnings :: [String]   -- Accumulated warnings
  , ctxMetas :: S.Set Name    -- Metavariable names (for uppercase refs)
  , ctxInEql :: Bool          -- Are we inside an Eql type? (use lowercase refs)
  }