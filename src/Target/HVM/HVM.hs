{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module      : Target.HVM
-- Description : Bend backend that emits HVM (KolmoC) programs
--
-- This module consolidates the former KolmoC backend into a single file and
-- exposes it as the HVM target.
module Target.HVM.HVM
  ( compile
  , CompileError(..)
  , HCore(..)
  ) where

import Control.Exception (throw)
import Control.Monad (foldM, unless, when)
import Core.Show (BendException(..))
import Core.Type hiding (Name)
import qualified Core.Type as Core
import Data.Char (isAlphaNum, ord, toUpper)
import Data.List (find, intercalate)
import Data.Word (Word32)
import Debug.Trace (trace)
import GHC.Generics (Generic)
import qualified Data.Map as M
import qualified Data.Set as S

-- ============================================================================
-- KolmoC core (re-exposed as the HVM backend)
-- ============================================================================

-- Type aliases for clarity
type Name = String
type Lab = String   -- 4-letter label for superpositions/dups
type Nick = String  -- 4-letter nick for definitions

-- KolmoC Core AST
-- Represents the core term structure of KolmoC
data HCore
  -- Variables
  = HVar Name            -- x (variable reference)
  | HDP0 Lab Name        -- x₀ (left dup reference)
  | HDP1 Lab Name        -- x₁ (right dup reference)

  -- Universe
  | HSet                 -- * (type universe)

  -- Functions
  | HAll HCore HCore     -- ∀A.B (dependent function type)
  | HLam Name HCore      -- λx.f (lambda abstraction)
  | HApp HCore HCore     -- (f x) (application)

  -- Superpositions
  | HEra                 -- &{} (eraser)
  | HSup Lab HCore HCore -- &L{x,y} (superposition)
  | HDup Lab Name Name HCore HCore -- !x&L=v; body (duplication/sharing)

  -- Unit
  | HUni                 -- ⊤ (unit type)
  | HNull                -- () (unit value)
  | HUse HCore           -- λ{():u} (unit eliminator)

  -- Booleans
  | HBit                 -- 𝔹 (bool type)
  | HBt0                 -- #0 (false)
  | HBt1                 -- #1 (true)
  | HBif HCore HCore     -- λ{#0:f;#1:t} (bool eliminator)

  -- Naturals
  | HNat                 -- ℕ (nat type)
  | HZer                 -- 0n (zero)
  | HSuc HCore           -- 1n+x (successor)
  | HInc HCore           -- ↑x (increment operator)
  | HNif HCore HCore     -- λ{0n:z;1n+:s} (nat eliminator)

  -- Unsigned 32-bit integers
  | HU32                 -- U32 (u32 type)
  | HUva Word32          -- numeric value (unboxed u32)
  | HUif HCore HCore     -- λ{0:z;1+:s} (u32 eliminator)

  -- Lists
  | HLst HCore           -- T[] (list type)
  | HNil                 -- [] (empty list)
  | HCon HCore HCore     -- x<>y (cons)
  | HMat HCore HCore     -- λ{[]:n;<>:c} (list eliminator)

  -- Equality
  | HEql HCore HCore HCore -- T{a==b} (equality type)
  | HRfl                 -- {==} (reflexivity)
  | HRwt HCore HCore HCore -- ~e:P;f (rewrite)

  -- Pairs
  | HSig HCore HCore     -- Σx.y (dependent pair type)
  | HTup HCore HCore     -- #(x,y) (pair value)
  | HGet HCore           -- λ{#(,):p} (pair eliminator)

  -- References
  | HRef Nick            -- @F (function reference)
  | HTyp Nick            -- @:F (type reference)

  -- Empty (bottom)
  | HEmp                 -- ⊥ (empty type)
  | HErf                 -- λ{} (empty match/absurdity)

  -- Special spinners (for call-by-name references)
  | HSpn Nick HCore      -- &fn(xs) (spinner for refs with args)

  -- Primitives (for operations that don't map directly)
  | HPri String [HCore]  -- Primitive operations with args

  -- Metavariables/Generators
  | HGen Nick HCore HCore HCore -- ?N ctx : typ #seed (program generator)
  deriving (Show, Eq, Generic)

-- Binary operations that KolmoC supports
data HOp2
  = H_ADD | H_SUB | H_MUL | H_DIV | H_MOD
  | H_EQ  | H_NEQ | H_LT  | H_GT  | H_LEQ | H_GEQ
  | H_AND | H_OR  | H_XOR | H_SHL | H_SHR
  deriving (Show, Eq)

-- A compiled definition
data HDefn = HDefn
  { hdefName :: Nick           -- Definition name (4-letter nick)
  , hdefType :: Maybe HCore    -- Optional type annotation
  , hdefBody :: HCore          -- Definition body
  } deriving (Show, Eq)

-- A book of compiled definitions
type HBook = M.Map Nick HDefn

-- Compilation errors
data HCompileError
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
type HResult a = Either HCompileError a

-- Helper to track compilation context
data CompileCtx = CompileCtx
  { ctxBook :: Book           -- Original Bend book
  , ctxDefs :: HBook          -- Accumulated KolmoC definitions
  , ctxFresh :: Int           -- Fresh name counter
  , ctxWarnings :: [String]   -- Accumulated warnings
  , ctxMetas :: S.Set Name    -- Metavariable names (for uppercase refs)
  , ctxInEql :: Bool          -- Are we inside an Eql type? (use lowercase refs)
  , ctxGens :: [Nick]         -- Ordered list of generator nicks
  }

-- ============================================================================
-- Public API
-- ============================================================================

-- Re-export error type for API
type CompileError = HCompileError

-- Main compilation function
-- Takes a Bend Book and main function name, produces HVM (KolmoC) source code
compile :: Book -> String -> String
compile book mainFQN =
  case compileBook book mainFQN of
    Left err -> throw (BendException $ CompilationError $ showError err)
    Right (hbook, mainNick) -> showHVM hbook mainNick

-- Format compilation errors
showError :: HCompileError -> String
showError err = case err of
  UnsupportedConstruct desc ->
    "Unsupported construct: " ++ desc ++ ". This feature is not available in the HVM backend."

  UnsupportedNumericType typ ->
    "Unsupported numeric type: " ++ typ ++ ". HVM only supports U32 integers."

  PatternMatchNotDesugared msg ->
    "Pattern match not desugared: " ++ msg ++ ". This is a compiler bug - pattern matches should be desugared before HVM compilation."

  IONotSupported msg ->
    "IO operations are not supported in the HVM backend: " ++ msg

  MetaVariableNotSupported msg ->
    "Meta variables are not supported in the HVM backend: " ++ msg

  ForkNotSupported msg ->
    "Fork constructs are not supported in the HVM backend: " ++ msg

  NumericConversionWarning msg val ->
    "Warning: " ++ msg ++ " (value: " ++ show val ++ ")"

  InvalidNick nick ->
    "Invalid nick: " ++ nick ++ ". Nicks must be 1-4 characters."

  UnknownReference ref ->
    "Unknown reference: " ++ ref

  DuplicateDefinition nick ->
    "Duplicate definition for nick: " ++ nick

-- ============================================================================
-- Compilation
-- ============================================================================

-- Main compilation entry point
compileBook :: Book -> String -> Either HCompileError (HBook, Nick)
compileBook book@(Book defs _) mainFQN = do
  -- Pre-scan to collect all metavariable names
  let metas = S.fromList [name | (name, (_, term, _)) <- M.toList defs, isMet (cut term)]
  let hasMain = M.member mainFQN defs
  let hasGen  = not (S.null metas)
  let ctx = CompileCtx book M.empty 0 [] metas False []
  -- Ensure we have an entry point unless generators will supply it
  unless (hasMain || hasGen) $
    Left $ UnknownReference $ "Main function not found: " ++ mainFQN
  -- Compile all definitions
  finalCtx <- foldM compileDefn ctx (M.toList defs)
  let gens = ctxGens finalCtx
  let mainNick = toNick mainFQN
  let finalDefs = case gens of
        [] -> ctxDefs finalCtx
        _  ->
          let targetNick = map toUpper (last gens)
              autoMain = HDefn mainNick Nothing (HRef targetNick)
          in M.insert mainNick autoMain (ctxDefs finalCtx)
  return (finalDefs, mainNick)
  where
    isMet (Met _ _ _) = True
    isMet _           = False

-- Compile a single definition
compileDefn :: CompileCtx -> (Core.Name, Defn) -> Either HCompileError CompileCtx
compileDefn ctx (name, (_, term, typ)) = do
  let nick = toNick name
  -- Check for duplicate
  when (M.member nick (ctxDefs ctx)) $
    Left $ DuplicateDefinition nick
  -- Check if this is a metavariable
  let isMeta = case cut term of
        Met _ _ _ -> True
        _         -> False
  -- Check if this is an assert (Rfl body with Eql type)
  let isAssert = case (cut term, cut typ) of
        (Rfl, Eql _ _ _) -> True
        _                -> False
  -- Compile the term body and the type
  hbody <- termToHCore ctx term
  let hbodyWithDup = autoDup hbody  -- Apply autodup pass
  htype <- if isMeta
    then return Nothing  -- Generators have types in their declaration, not definition
    else Just <$> termToHCore ctx typ  -- Compile type for regular defs and asserts
  let hdef = HDefn nick htype hbodyWithDup
  -- Add to metas set if it's a metavariable
  let updatedMetas = if isMeta then S.insert name (ctxMetas ctx) else ctxMetas ctx
  let updatedGens  = if isMeta then ctxGens ctx ++ [nick] else ctxGens ctx
  let updatedCtx = ctx { ctxDefs = M.insert nick hdef (ctxDefs ctx)
                       , ctxMetas = updatedMetas
                       , ctxGens = updatedGens }
  return updatedCtx

-- Convert Bend Term to KolmoC Core
termToHCore :: CompileCtx -> Term -> Either HCompileError HCore
termToHCore ctx term = case cut term of
  -- Variables and references
  Var n _     -> return $ HVar n
  Ref k _     ->
    -- If k is a metavariable, use uppercase nick (unless inside Eql)
    let nick = toNick k
        isMeta = S.member k (ctxMetas ctx)
        shouldUppercase = isMeta && not (ctxInEql ctx)
        finalNick = if shouldUppercase then map toUpper nick else nick
    in return $ HRef finalNick
  Sub t       -> termToHCore ctx t

  -- Functions
  Lam n _ f   -> do
    body <- termToHCore ctx (f (Var n 0))
    return $ HLam n body

  App f x     -> do
    hf <- termToHCore ctx f
    hx <- termToHCore ctx x
    return $ HApp hf hx

  All t f     -> do
    ht <- termToHCore ctx t
    case f of
      Lam n _ g -> do
        hbody <- termToHCore ctx (g (Var n 0))
        return $ HAll ht (HLam n hbody)
      _ -> do
        hf <- termToHCore ctx f
        return $ HAll ht hf

  -- Fix point - create global definition
  Fix n f -> do
    -- For now, just inline the fix
    -- TODO: Create actual global def with fresh name
    body <- termToHCore ctx (f (Var n 0))
    return $ HLam n (HApp body (HVar n))

  -- Superpositions
  Era         -> return HEra
  Sup l a b   -> do
    ha <- termToHCore ctx a
    hb <- termToHCore ctx b
    return $ HSup (labToStr l) ha hb

  -- SupM becomes a Dup with same label
  SupM l f    -> case cut f of
    Lam a _ (subst a -> Lam b _ (subst b -> body)) -> do
      let lab = labToStr l
      hbody <- termToHCore ctx body
      return $ HDup lab a b (HSup lab (HVar a) (HVar b)) hbody
    _ -> do
      -- If not in expected form, create with fresh names
      let lab = labToStr l
      hf <- termToHCore ctx f
      return $ HDup lab "x" "y" (HSup lab (HVar "x") (HVar "y"))
                    (HApp (HApp hf (HVar "x")) (HVar "y"))

  -- Universe and types
  Set         -> return HSet

  -- Unit
  Uni         -> return HUni
  One         -> return HNull
  UniM f      -> do
    hf <- termToHCore ctx f
    return $ HUse hf

  -- Booleans
  Bit         -> return HBit
  Bt0         -> return HBt0
  Bt1         -> return HBt1
  BitM f t    -> do
    hf <- termToHCore ctx f
    ht <- termToHCore ctx t
    return $ HBif hf ht

  -- Naturals
  Nat         -> return HNat
  Zer         -> return HZer
  Suc n       -> do
    hn <- termToHCore ctx n
    return $ HSuc hn
  NatM z s    -> do
    hz <- termToHCore ctx z
    hs <- termToHCore ctx s
    return $ HNif hz hs

  -- Lists
  Lst t       -> do
    ht <- termToHCore ctx t
    return $ HLst ht
  Nil         -> return HNil
  Con h t     -> do
    hh <- termToHCore ctx h
    ht <- termToHCore ctx t
    return $ HCon hh ht
  LstM n c    -> do
    hn <- termToHCore ctx n
    hc <- termToHCore ctx c
    return $ HMat hn hc

  -- Numbers
  Num _       -> return HU32
  Val v       -> case v of
    U64_V n   -> do
      let u32val = fromIntegral n :: Word32
      when (n > fromIntegral (maxBound :: Word32)) $
        trace ("Warning: U64 value " ++ show n ++ " truncated to U32") (return ())
      return $ HUva u32val
    I64_V n   -> do
      let u32val = fromIntegral n :: Word32
      trace ("Warning: I64 value " ++ show n ++ " converted to U32") $
        return $ HUva u32val
    CHR_V c   -> return $ HUva (fromIntegral (ord c))
    F64_V _   -> Left $ UnsupportedNumericType "F64"

  Op2 op a b  -> do
    ha <- termToHCore ctx a
    hb <- termToHCore ctx b
    return $ HPri (op2ToHOp op) [ha, hb]

  Op1 op a    -> Left $ UnsupportedConstruct $ "Unary operation: " ++ show op

  -- Pairs
  Sig t f     -> do
    ht <- termToHCore ctx t
    hf <- termToHCore ctx f
    return $ HSig ht hf
  Tup a b     -> do
    ha <- termToHCore ctx a
    hb <- termToHCore ctx b
    return $ HTup ha hb
  SigM f      -> do
    hf <- termToHCore ctx f
    return $ HGet hf

  -- Equality
  Eql t a b   -> do
    -- Inside Eql, use lowercase refs for metavariables (for generator tests)
    let ctxInEql = ctx { ctxInEql = True }
    ht <- termToHCore ctxInEql t
    ha <- termToHCore ctxInEql a
    hb <- termToHCore ctxInEql b
    return $ HEql ht ha hb
  Rfl         -> return HRfl
  EqlM f      -> do
    hf <- termToHCore ctx f
    -- EqlM is a match on equality, just apply the function
    return hf
  -- Rewrite: Bend's `rewrite e f` where e : T{a==b}
  -- At runtime, KolmoC erases rewrites: ~e:P;f → f
  -- The motive P is implicit in Bend (derived from the goal during type checking)
  -- Since we don't have access to the goal here, and KolmoC erases rewrites anyway,
  -- we just compile to the body f directly. This is semantically correct.
  Rwt _ f     -> termToHCore ctx f

  -- Empty
  Emp         -> return HEmp
  EmpM        -> return HErf

  -- Primitives
  Pri p       -> return $ HPri (priToHPri p) []

  -- Logging (compile to identity)
  Log _ x     -> termToHCore ctx x

  -- Location (strip)
  Loc _ t     -> termToHCore ctx t

  -- Check and trust (strip)
  Chk v _     -> termToHCore ctx v
  Tst v       -> termToHCore ctx v

  -- Use (inline)
  Let _ _ v f -> do
    hv <- termToHCore ctx v
    hf <- termToHCore ctx (f v)
    return $ HApp (HLam "_" hf) hv

  Use _ v f   -> termToHCore ctx (f v)

  -- Unsupported constructs
  Pat _ _ _   -> Left $ PatternMatchNotDesugared "Pattern match should be desugared"
  IO _        -> Left $ IONotSupported "IO operations not supported"
  -- Metavariables/Generators
  Met name typ metCtx -> do
    -- Compile the type signature
    htyp <- termToHCore ctx typ
    -- Build context list from references
    hctx <- compileMetContext ctx metCtx
    -- Get metavariable nick
    let nick = toNick name
    -- Create GEN term with default seed 0
    return $ HGen nick hctx htyp (HUva 0)
  Frk _ _ _   -> Left $ ForkNotSupported "Fork constructs not supported"

  -- Enums - compile to strings/symbols for now
  Enu _       -> return HSet  -- Enum type becomes Set
  Sym s       -> return $ HPri ("SYM:" ++ s) []
  EnuM _ _    -> Left $ UnsupportedConstruct "Enum match"

-- Helper to extract body from lambda with substitution
subst :: Core.Name -> (Term -> Term) -> Term
subst n f = f (Var n 0)

-- Convert Term label to string
labToStr :: Term -> Lab
labToStr term = case term of
  Sub t   -> labToStr t
  Var n _ -> n
  _       -> case cut term of
    Var n _ -> n
    _       -> "LABL"

-- Convert FQN to KolmoC name
-- Takes last significant part after :: and cleans it for KolmoC syntax
toNick :: String -> Nick
toNick name =
  let parts = splitOn "::" name
      lastPart = if null parts then name else last parts
      -- Replace invalid chars with underscore, keep alphanumeric and underscore
      clean = map (\c -> if isAlphaNum c || c == '_' then c else '_') lastPart
  in clean
  where
    splitOn :: String -> String -> [String]
    splitOn _ [] = [""]
    splitOn delim str =
      let (before, remainder) = breakOn delim str
      in if null remainder
         then [before]
         else before : splitOn delim (drop (length delim) remainder)
    breakOn :: String -> String -> (String, String)
    breakOn delim str = go "" str
      where
        go acc [] = (acc, "")
        go acc s@(c:cs)
          | take (length delim) s == delim = (acc, s)
          | otherwise = go (acc ++ [c]) cs

-- Convert NOp2 to KolmoC operation string
op2ToHOp :: NOp2 -> String
op2ToHOp ADD = "ADD"
op2ToHOp SUB = "SUB"
op2ToHOp MUL = "MUL"
op2ToHOp DIV = "DIV"
op2ToHOp MOD = "MOD"
op2ToHOp EQL = "EQ"
op2ToHOp NEQ = "NEQ"
op2ToHOp LST = "LT"
op2ToHOp GRT = "GT"
op2ToHOp LEQ = "LEQ"
op2ToHOp GEQ = "GEQ"
op2ToHOp AND = "AND"
op2ToHOp OR  = "OR"
op2ToHOp XOR = "XOR"
op2ToHOp SHL = "SHL"
op2ToHOp SHR = "SHR"
op2ToHOp POW = "POW"

-- Convert NOp1 to KolmoC operation string
op1ToHOp :: NOp1 -> String
op1ToHOp NOT = "NOT"
op1ToHOp NEG = "NEG"

-- Convert PriF to KolmoC primitive string
priToHPri :: PriF -> String
priToHPri U64_TO_CHAR     = "U64_TO_CHAR"
priToHPri CHAR_TO_U64     = "CHAR_TO_U64"
priToHPri HVM_INC         = "INC"
priToHPri HVM_DEC         = "DEC"
priToHPri IO_PURE         = "IO_PURE"
priToHPri IO_BIND         = "IO_BIND"
priToHPri IO_PRINT        = "IO_PRINT"
priToHPri IO_PUTC         = "IO_PUTC"
priToHPri IO_GETC         = "IO_GETC"
priToHPri IO_READ_FILE    = "IO_READ_FILE"
priToHPri IO_WRITE_FILE   = "IO_WRITE_FILE"

-- Metavariable context compilation
-- Compile Met context: [Term] -> List of (Var, TypeRef) pairs
compileMetContext :: CompileCtx -> [Term] -> Either HCompileError HCore
compileMetContext ctx terms = buildList terms
  where
    buildList [] = return HNil
    buildList (t:ts) = do
      rest <- buildList ts
      pair <- termToContextPair ctx t
      return $ HCon pair rest

-- Convert a single context term to (var, typeref) pair
termToContextPair :: CompileCtx -> Term -> Either HCompileError HCore
termToContextPair ctx term = case cut term of
  Ref k _ -> do
    -- Get the reference name and create tuple: #(var, @:ref)
    let refNick = toNick k
    let varName = refNick  -- Use ref name as variable
    return $ HTup (HVar varName) (HTyp refNick)

  _ -> Left $ UnsupportedConstruct
    "Metavariable context term must be a reference (expected Ref)"

-- ============================================================================
-- AUTODUP: Automatic DUP insertion for non-linear variable usage
-- ============================================================================

-- Main autodup pass - recursively process HCore and insert DUPs for non-linear vars
autoDup :: HCore -> HCore
autoDup term = case term of
  -- Lambda: check if variable is used multiple times
  HLam name body ->
    let processedBody = autoDup body  -- Recursively process body first
        count = countUsage name processedBody
    in if count <= 1
       then HLam name processedBody
       else HLam name (insertDupChain name count processedBody)

  -- Recursively process all other constructors
  HApp f x     -> HApp (autoDup f) (autoDup x)
  HAll t b     -> HAll (autoDup t) (autoDup b)
  HSup l a b   -> HSup l (autoDup a) (autoDup b)
  HDup l x y v b -> HDup l x y (autoDup v) (autoDup b)
  HUse u       -> HUse (autoDup u)
  HBif f t     -> HBif (autoDup f) (autoDup t)
  HNif z s     -> HNif (autoDup z) (autoDup s)
  HUif z s     -> HUif (autoDup z) (autoDup s)
  HCon h t     -> HCon (autoDup h) (autoDup t)
  HMat n c     -> HMat (autoDup n) (autoDup c)
  HEql t a b   -> HEql (autoDup t) (autoDup a) (autoDup b)
  HRwt e p f   -> HRwt (autoDup e) (autoDup p) (autoDup f)
  HSig t f     -> HSig (autoDup t) (autoDup f)
  HTup a b     -> HTup (autoDup a) (autoDup b)
  HGet p       -> HGet (autoDup p)
  HSuc n       -> HSuc (autoDup n)
  HInc n       -> HInc (autoDup n)
  HLst t       -> HLst (autoDup t)
  HSpn n x     -> HSpn n (autoDup x)
  HPri op args -> HPri op (map autoDup args)
  HGen n c t s -> HGen n (autoDup c) (autoDup t) (autoDup s)

  -- Atoms (no recursion needed)
  _ -> term

-- Count how many times a variable is used (respecting shadowing)
countUsage :: Nick -> HCore -> Int
countUsage var term = case term of
  HVar n | n == var -> 1
         | otherwise -> 0
  HDP0 _ n | n == var -> 1
           | otherwise -> 0
  HDP1 _ n | n == var -> 1
           | otherwise -> 0

  -- Lambda shadows the variable if names match
  HLam n body | n == var -> 0
              | otherwise -> countUsage var body

  -- Recursively count in compound terms
  HApp f x     -> countUsage var f + countUsage var x
  HAll t b     -> countUsage var t + countUsage var b
  HSup _ a b   -> countUsage var a + countUsage var b
  HDup _ x y v b -> countUsage var v + countUsage var b
  HUse u       -> countUsage var u
  HBif f t     -> countUsage var f + countUsage var t
  HNif z s     -> countUsage var z + countUsage var s
  HUif z s     -> countUsage var z + countUsage var s
  HCon h t     -> countUsage var h + countUsage var t
  HMat n c     -> countUsage var n + countUsage var c
  HEql t a b   -> countUsage var t + countUsage var a + countUsage var b
  HRwt e p f   -> countUsage var e + countUsage var p + countUsage var f
  HSig t f     -> countUsage var t + countUsage var f
  HTup a b     -> countUsage var a + countUsage var b
  HGet p       -> countUsage var p
  HSuc n       -> countUsage var n
  HInc n       -> countUsage var n
  HLst t       -> countUsage var t
  HSpn _ x     -> countUsage var x
  HPri _ args  -> sum (map (countUsage var) args)
  HGen _ c t s -> countUsage var c + countUsage var t + countUsage var s

  -- Atoms don't contain variables
  _ -> 0

-- Insert DUP chain for a variable used N times (N >= 2)
-- Pattern: !D1_v&v = v; !D2_v&v = D1_v₁; ... ; body[v₁→D1_v₀, v₂→D2_v₀, ..., vₙ→Dₙ₋₁₁]
insertDupChain :: Nick -> Int -> HCore -> HCore
insertDupChain var count body =
  let dupNames = ["D" ++ show i ++ "_" ++ var | i <- [1..count-1]]
      bodyWithSubst = substituteOccurrences var dupNames body 0
  in wrapDups var dupNames bodyWithSubst

-- Wrap body with DUP chain
-- For dupNames = [D1_a, D2_a], generates:
--   !D1_a&a = a; !D2_a&a = D1_a₁; body
wrapDups :: Nick -> [Nick] -> HCore -> HCore
wrapDups _ [] body = body
wrapDups var [d1] body =
  HDup var d1 "_" (HVar var) body
wrapDups var (d1:rest) body =
  HDup var d1 "_" (HVar var) (wrapDups' var d1 rest body)
  where
    wrapDups' _ _ [] b = b
    wrapDups' v prev (d:ds) b =
      HDup v d "_" (HDP1 v prev) (wrapDups' v d ds b)

-- Substitute occurrences of variable with DP0/DP1 references
-- occurrence i → Di₀, final occurrence → Dₙ₋₁₁
substituteOccurrences :: Nick -> [Nick] -> HCore -> Int -> HCore
substituteOccurrences var dupNames body occNum =
  fst $ subst var dupNames body occNum
  where
    subst v dups term n = case term of
      HVar name | name == v ->
        let dupIdx = n
            ref = if dupIdx < length dups
                  then HDP0 v (dups !! dupIdx)
                  else HDP1 v (last dups)
        in (ref, n + 1)
      HVar name -> (HVar name, n)

      HDP0 l name -> (HDP0 l name, n)
      HDP1 l name -> (HDP1 l name, n)

      -- Lambda shadows if names match
      HLam name lamBody | name == v -> (HLam name lamBody, n)
                        | otherwise ->
        let (substBody, nextN) = subst v dups lamBody n
        in (HLam name substBody, nextN)

      -- Recursively substitute in compound terms
      HApp f x ->
        let (substF, n1) = subst v dups f n
            (substX, n2) = subst v dups x n1
        in (HApp substF substX, n2)

      HAll t b ->
        let (substT, n1) = subst v dups t n
            (substB, n2) = subst v dups b n1
        in (HAll substT substB, n2)

      HSup l a b ->
        let (substA, n1) = subst v dups a n
            (substB, n2) = subst v dups b n1
        in (HSup l substA substB, n2)

      HDup l x y val dupBody ->
        let (substVal, n1) = subst v dups val n
            (substDupBody, n2) = subst v dups dupBody n1
        in (HDup l x y substVal substDupBody, n2)

      HUse u ->
        let (substU, n1) = subst v dups u n
        in (HUse substU, n1)

      HBif f t ->
        let (substF, n1) = subst v dups f n
            (substT, n2) = subst v dups t n1
        in (HBif substF substT, n2)

      HNif z s ->
        let (substZ, n1) = subst v dups z n
            (substS, n2) = subst v dups s n1
        in (HNif substZ substS, n2)

      HUif z s ->
        let (substZ, n1) = subst v dups z n
            (substS, n2) = subst v dups s n1
        in (HUif substZ substS, n2)

      HCon h t ->
        let (substH, n1) = subst v dups h n
            (substT, n2) = subst v dups t n1
        in (HCon substH substT, n2)

      HMat m c ->
        let (substM, n1) = subst v dups m n
            (substC, n2) = subst v dups c n1
        in (HMat substM substC, n2)

      HEql t a b ->
        let (substT, n1) = subst v dups t n
            (substA, n2) = subst v dups a n1
            (substB, n3) = subst v dups b n2
        in (HEql substT substA substB, n3)

      HRwt e p f ->
        let (substE, n1) = subst v dups e n
            (substP, n2) = subst v dups p n1
            (substF, n3) = subst v dups f n2
        in (HRwt substE substP substF, n3)

      HSig t f ->
        let (substT, n1) = subst v dups t n
            (substF, n2) = subst v dups f n1
        in (HSig substT substF, n2)

      HTup a b ->
        let (substA, n1) = subst v dups a n
            (substB, n2) = subst v dups b n1
        in (HTup substA substB, n2)

      HGet p ->
        let (substP, n1) = subst v dups p n
        in (HGet substP, n1)

      HSuc s ->
        let (substS, n1) = subst v dups s n
        in (HSuc substS, n1)

      HInc i ->
        let (substI, n1) = subst v dups i n
        in (HInc substI, n1)

      HLst t ->
        let (substT, n1) = subst v dups t n
        in (HLst substT, n1)

      HSpn name x ->
        let (substX, n1) = subst v dups x n
        in (HSpn name substX, n1)

      HPri op args ->
        let (substArgs, nextN) = substList v dups args n
        in (HPri op substArgs, nextN)

      HGen name c t s ->
        let (substC, n1) = subst v dups c n
            (substT, n2) = subst v dups t n1
            (substS, n3) = subst v dups s n2
        in (HGen name substC substT substS, n3)

      -- Atoms
      _ -> (term, n)

    substList _ _ [] n = ([], n)
    substList v dups (x:xs) n =
      let (substX, n1) = subst v dups x n
          (substXs, n2) = substList v dups xs n1
      in (substX:substXs, n2)

-- ============================================================================
-- Pretty-printing
-- ============================================================================

-- Pretty print a KolmoC book with all definitions
showHBook :: HBook -> Nick -> String
showHBook hbook mainNick =
  let defs = M.toList hbook
      -- Classify definitions
      isGen (_, HDefn _ _ (HGen _ _ _ _)) = True
      isGen _ = False
      isAssert (_, HDefn _ (Just (HEql _ _ _)) HRfl) = True
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
  in unlines $ map showHDefn allDefs
  where
    partition p xs = (filter p xs, filter (not . p) xs)

-- Pretty print a single definition
showHDefn :: (Nick, HDefn) -> String
showHDefn (_, HDefn nick mtyp body) =
  -- Check if body is a generator - print as declaration, not definition
  case body of
    HGen genNick ctx typ seed ->
      "?" ++ genNick ++ showGenCtx ctx ++ " : " ++ showHCore 0 typ ++ showGenSeed seed ++ ";"
    HRfl -> case mtyp of
      -- Assert: body is Rfl and type is Eql - print as !Type{lhs==rhs};
      Just (HEql typ lhs rhs) ->
        "!" ++ paren (showHCore 0 typ)
          ++ "{" ++ showHCore 0 lhs ++ "==" ++ showHCore 0 rhs ++ "};"
      _ -> -- Regular definition with Rfl body
        case mtyp of
          Nothing -> "@" ++ nick ++ " = " ++ showHCore 0 body ++ " ;"
          Just typ -> "@" ++ nick ++ " : " ++ showHCore 0 typ ++ " = " ++ showHCore 0 body ++ " ;"
    -- Main reference (uppercase) - no type annotation
    HRef name | all (`elem` ['A'..'Z']) name -> "@" ++ nick ++ " = " ++ showHCore 0 body ++ " ;"
    _ -> case mtyp of
      Nothing -> "@" ++ nick ++ " = " ++ showHCore 0 body ++ " ;"
      Just typ -> "@" ++ nick ++ " : " ++ showHCore 0 typ ++ " = " ++ showHCore 0 body ++ " ;"
  where
    -- Show generator context (extract variable names from tuple list)
    showGenCtx HNil = "[]"
    showGenCtx ctx = "[" ++ intercalate ", " (extractCtxNames ctx) ++ "]"

    extractCtxNames :: HCore -> [String]
    extractCtxNames HNil = []
    extractCtxNames (HCon (HTup (HVar name) _) rest) = ("@" ++ name) : extractCtxNames rest
    extractCtxNames (HCon (HTup (HRef name) _) rest) = ("@" ++ name) : extractCtxNames rest
    extractCtxNames _ = []  -- Fallback for unexpected structure

    -- Show generator seed (omit if 0)
    showGenSeed (HUva 0) = ""
    showGenSeed (HUva n) = " #" ++ showBinary n
    showGenSeed s = " #" ++ showHCore 0 s

    showBinary n = reverse $ go n
      where
        go 0 = "0"
        go 1 = "1"
        go x = (if x `mod` 2 == 1 then '1' else '0') : go (x `div` 2)

-- Pretty print a HCore term with indentation level
showHCore :: Int -> HCore -> String
showHCore i term = case term of
  -- Variables
  HVar n       -> n
  HDP0 _ n     -> n ++ "₀"  -- Using subscript 0
  HDP1 _ n     -> n ++ "₁"  -- Using subscript 1

  -- Universe
  HSet         -> "*"

  -- Functions (with arrow sugar)
  HAll t b     -> showFunctionType t b
  HLam n b     -> "λ" ++ n ++ "." ++ showHCore i b
  -- Application with flattening for cleaner output
  HApp f x     ->
    let (fn, args) = flattenApp term
    in case fn of
         HRef _ -> "(" ++ showHCore i fn ++ concatMap (\a -> " " ++ showAtom i a) args ++ ")"
         _      -> "(" ++ showHCore i f ++ " " ++ showAtom i x ++ ")"

  -- Superpositions
  HEra         -> "&{}"
  HSup l a b   -> "&" ++ l ++ "{" ++ showHCore i a ++ "," ++ showHCore i b ++ "}"
  HDup l x y v b -> "!" ++ x ++ "&" ++ l ++ " = " ++ showHCore i v ++ "; " ++ showHCore i b

  -- Unit
  HUni         -> "⊤"
  HNull        -> "()"
  HUse u       -> "λ{():" ++ showHCore i u ++ "}"

  -- Booleans
  HBit         -> "𝔹"
  HBt0         -> "#0"
  HBt1         -> "#1"
  HBif f t     -> "λ{#0:" ++ showHCore i f ++ ";#1:" ++ showHCore i t ++ "}"

  -- Naturals (with numeric sugar)
  HNat         -> "ℕ"
  HZer         -> "0n"
  HSuc n       -> case natToNumber (HSuc n) of
                    Just num -> show num ++ "n"
                    Nothing  -> "1n+" ++ showAtom i n
  HInc n       -> "↑" ++ paren (showHCore i n)
  HNif z s     -> "λ{0n:" ++ showHCore i z ++ ";1n+:" ++ showHCore i s ++ "}"

  -- U32
  HU32         -> "U32"
  HUva n       -> show n
  HUif z s     -> "λ{0:" ++ showHCore i z ++ ";1+:" ++ showHCore i s ++ "}"

  -- Lists (with list sugar)
  HLst t       -> paren (showHCore i t) ++ "[]"
  HNil         -> "[]"
  HCon h t     -> case listToElements (HCon h t) of
                    Just elems -> "[" ++ intercalate "," (map (showHCore i) elems) ++ "]"
                    Nothing    -> showConsHead i h ++ " <> " ++ showConsTail i t
  HMat n c     -> "λ{[]:" ++ showHCore i n ++ ";<>:" ++ showHCore i c ++ "}"

  -- Equality
  HEql t a b   -> paren (showHCore i t) ++ "{" ++ showHCore i a ++ "==" ++ showHCore i b ++ "}"
  HRfl         -> "{==}"
  HRwt e p f   -> "~" ++ paren (showHCore i e) ++ ":" ++ paren (showHCore i p) ++ ";" ++ showHCore i f

  -- Pairs
  HSig t f     -> "Σ" ++ paren (showHCore i t) ++ "." ++ showHCore i f
  HTup a b     -> "#(" ++ showHCore i a ++ "," ++ showHCore i b ++ ")"
  HGet p       -> "λ{#(,):" ++ showHCore i p ++ "}"

  -- References
  HRef n       -> "@" ++ n
  HTyp n       -> "@:" ++ n

  -- Empty
  HEmp         -> "⊥"
  HErf         -> "λ{}"

  -- Spinners
  HSpn n x     -> "&" ++ n ++ "(" ++ showHCore i x ++ ")"

  -- Primitives (custom handling for special operations)
  HPri op args -> showPrimitive op args i

  -- Metavariables/Generators
  HGen nick ctx typ seed ->
    "?" ++ nick ++ " " ++ showHCore i ctx ++ " : " ++ showHCore i typ ++ showSeed seed
    where
      showSeed (HUva 0) = ""  -- Omit default seed
      showSeed (HUva n) = " #" ++ showBinary n
      showSeed s = " #" ++ paren (showHCore i s)

      showBinary n = reverse $ go n
        where
          go 0 = "0"
          go 1 = "1"
          go x = (if x `mod` 2 == 1 then '1' else '0') : go (x `div` 2)

-- Helper to add parentheses when needed
paren :: String -> String
paren s = if needsParen s then "(" ++ s ++ ")" else s
  where
    needsParen str = ' ' `elem` str || any (`elem` str) "λ∀Σ"

-- Show primitive operations
showPrimitive :: String -> [HCore] -> Int -> String
showPrimitive op args i = case (op, args) of
  -- Binary operations
  ("ADD", [a, b]) -> "(" ++ showHCore i a ++ " + " ++ showHCore i b ++ ")"
  ("SUB", [a, b]) -> "(" ++ showHCore i a ++ " - " ++ showHCore i b ++ ")"
  ("MUL", [a, b]) -> "(" ++ showHCore i a ++ " * " ++ showHCore i b ++ ")"
  ("DIV", [a, b]) -> "(" ++ showHCore i a ++ " / " ++ showHCore i b ++ ")"
  ("MOD", [a, b]) -> "(" ++ showHCore i a ++ " % " ++ showHCore i b ++ ")"
  ("EQ",  [a, b]) -> "(" ++ showHCore i a ++ " == " ++ showHCore i b ++ ")"
  ("NEQ", [a, b]) -> "(" ++ showHCore i a ++ " != " ++ showHCore i b ++ ")"
  ("LT",  [a, b]) -> "(" ++ showHCore i a ++ " < " ++ showHCore i b ++ ")"
  ("GT",  [a, b]) -> "(" ++ showHCore i a ++ " > " ++ showHCore i b ++ ")"
  ("LEQ", [a, b]) -> "(" ++ showHCore i a ++ " <= " ++ showHCore i b ++ ")"
  ("GEQ", [a, b]) -> "(" ++ showHCore i a ++ " >= " ++ showHCore i b ++ ")"
  ("AND", [a, b]) -> "(" ++ showHCore i a ++ " & " ++ showHCore i b ++ ")"
  ("OR",  [a, b]) -> "(" ++ showHCore i a ++ " | " ++ showHCore i b ++ ")"
  ("XOR", [a, b]) -> "(" ++ showHCore i a ++ " ^ " ++ showHCore i b ++ ")"
  ("SHL", [a, b]) -> "(" ++ showHCore i a ++ " << " ++ showHCore i b ++ ")"
  ("SHR", [a, b]) -> "(" ++ showHCore i a ++ " >> " ++ showHCore i b ++ ")"

  -- Unary operations
  ("NOT", [a])    -> "(!" ++ showHCore i a ++ ")"
  ("NEG", [a])    -> "(-" ++ showHCore i a ++ ")"
  ("INC", [a])    -> "↑" ++ paren (showHCore i a)
  ("DEC", [a])    -> "↓" ++ paren (showHCore i a)

  -- Special primitives
  ("U64_TO_CHAR", [a]) -> "/u64_to_char(" ++ showHCore i a ++ ")"
  ("CHAR_TO_U64", [a]) -> "/char_to_u64(" ++ showHCore i a ++ ")"

  -- Symbols (enum constructors)
  (sym, []) | take 4 sym == "SYM:" -> "'" ++ drop 4 sym ++ "'"

  -- Default: show as primitive call
  _ -> "/" ++ op ++ if null args
                     then ""
                     else "(" ++ intercalate "," (map (showHCore i) args) ++ ")"

-- Sugar helpers
-- Convert function type ∀A.λx.B to A → B
showFunctionType :: HCore -> HCore -> String
showFunctionType argType body = case body of
  HLam name rest
    | name == "_" -> showHCore 0 argType ++ " → " ++ showHCore 0 rest
    | otherwise   -> "∀" ++ binder ++ ". " ++ showHCore 0 rest
    where
      binder = name ++ ": " ++ showHCore 0 argType
  _ -> "∀_: " ++ showHCore 0 argType ++ ". " ++ showHCore 0 body

-- Convert natural number chains to integers
natToNumber :: HCore -> Maybe Int
natToNumber HZer = Just 0
natToNumber (HSuc n) = fmap (+1) (natToNumber n)
natToNumber _ = Nothing

-- Convert list construction to list of elements
listToElements :: HCore -> Maybe [HCore]
listToElements HNil = Just []
listToElements (HCon h t) = fmap (h:) (listToElements t)
listToElements _ = Nothing

-- Flatten application chains for cleaner printing
-- (@f a b c) instead of (((f a) b) c)
flattenApp :: HCore -> (HCore, [HCore])
flattenApp (HApp f x) =
  let (fn, args) = flattenApp f
  in (fn, args ++ [x])
flattenApp term = (term, [])

-- Show a term as an atom (wrap in parens if it's compound)
showAtom :: Int -> HCore -> String
showAtom i term = case term of
  -- Atomic terms (no parens needed)
  HVar _ -> showHCore i term
  HDP0 _ _ -> showHCore i term
  HDP1 _ _ -> showHCore i term
  HRef _ -> showHCore i term
  HBt0 -> showHCore i term
  HBt1 -> showHCore i term
  HZer -> showHCore i term
  HNull -> showHCore i term
  HRfl -> showHCore i term
  HNil -> showHCore i term
  HUva _ -> showHCore i term
  -- Terms that add their own parens
  HApp _ _ -> showHCore i term
  -- Sugar forms that are atomic
  _ | Just _ <- listToElements term -> showHCore i term
  _ | Just _ <- natToNumber term -> showHCore i term
  -- Everything else needs parens
  _ -> "(" ++ showHCore i term ++ ")"

-- Show cons head with parens for successors
showConsHead :: Int -> HCore -> String
showConsHead i h = case h of
  HSuc _ -> "(" ++ showHCore i h ++ ")"
  _      -> showAtom i h

-- Show cons tail - applications already have parens from showHCore
showConsTail :: Int -> HCore -> String
showConsTail i t = showAtom i t

-- Export main show function
showHVM :: HBook -> Nick -> String
showHVM = showHBook
