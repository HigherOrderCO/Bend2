{-# LANGUAGE ViewPatterns #-}

module Target.KolmoC.Compile where

import Control.Monad (forM, foldM, unless, when)
import Data.Char (isAlphaNum, ord)
import Data.List (find)
import Data.Word (Word32)
import qualified Data.Map as M
import Debug.Trace

import Core.Type hiding (Name)
import qualified Core.Type as Core
import Target.KolmoC.Type

-- Main compilation entry point
compileBook :: Book -> String -> Either KCompileError (KBook, Nick)
compileBook book@(Book defs _) mainFQN = do
  let ctx = CompileCtx book M.empty 0 []
  -- Check main exists
  unless (M.member mainFQN defs) $
    Left $ UnknownReference $ "Main function not found: " ++ mainFQN
  -- Compile all definitions
  ctx' <- foldM compileDefn ctx (M.toList defs)
  -- Get main nick
  let mainNick = toNick mainFQN
  return (ctxDefs ctx', mainNick)

-- Compile a single definition
compileDefn :: CompileCtx -> (Core.Name, Defn) -> Either KCompileError CompileCtx
compileDefn ctx (name, (_, term, typ)) = do
  let nick = toNick name
  -- Check for duplicate
  when (M.member nick (ctxDefs ctx)) $
    Left $ DuplicateDefinition nick
  -- Compile the term body
  kbody <- termToKCore ctx term
  -- For now, ignore type (untyped compilation)
  let kdef = KDefn nick Nothing kbody
  let ctx' = ctx { ctxDefs = M.insert nick kdef (ctxDefs ctx) }
  return ctx'

-- Convert Bend Term to KolmoC Core
termToKCore :: CompileCtx -> Term -> Either KCompileError KCore
termToKCore ctx term = case cutTerm term of
  -- Variables and references
  Var n _     -> return $ KVar n
  Ref k _     -> return $ KRef (toNick k)
  Sub t       -> termToKCore ctx t

  -- Functions
  Lam n _ f   -> do
    body <- termToKCore ctx (f (Var n 0))
    return $ KLam n body

  App f x     -> do
    kf <- termToKCore ctx f
    kx <- termToKCore ctx x
    return $ KApp kf kx

  All t f     -> do
    kt <- termToKCore ctx t
    case f of
      Lam n _ g -> do
        kbody <- termToKCore ctx (g (Var n 0))
        return $ KAll kt (KLam n kbody)
      _ -> do
        kf <- termToKCore ctx f
        return $ KAll kt kf

  -- Fix point - create global definition
  Fix n f -> do
    -- For now, just inline the fix
    -- TODO: Create actual global def with fresh name
    body <- termToKCore ctx (f (Var n 0))
    return $ KLam n (KApp body (KVar n))

  -- Superpositions
  Era         -> return KEra
  Sup l a b   -> do
    ka <- termToKCore ctx a
    kb <- termToKCore ctx b
    return $ KSup (labToStr l) ka kb

  -- SupM becomes a Dup with same label
  SupM l f    -> case cutTerm f of
    Lam a _ (subst a -> Lam b _ (subst b -> body)) -> do
      let lab = labToStr l
      kbody <- termToKCore ctx body
      return $ KDup lab a b (KSup lab (KVar a) (KVar b)) kbody
    _ -> do
      -- If not in expected form, create with fresh names
      let lab = labToStr l
      kf <- termToKCore ctx f
      return $ KDup lab "x" "y" (KSup lab (KVar "x") (KVar "y"))
                    (KApp (KApp kf (KVar "x")) (KVar "y"))

  -- Universe and types
  Set         -> return KSet

  -- Unit
  Uni         -> return KUni
  One         -> return KNul
  UniM f      -> do
    kf <- termToKCore ctx f
    return $ KUse kf

  -- Booleans
  Bit         -> return KBit
  Bt0         -> return KBt0
  Bt1         -> return KBt1
  BitM f t    -> do
    kf <- termToKCore ctx f
    kt <- termToKCore ctx t
    return $ KBif kf kt

  -- Naturals
  Nat         -> return KNat
  Zer         -> return KZer
  Suc n       -> do
    kn <- termToKCore ctx n
    return $ KSuc kn
  NatM z s    -> do
    kz <- termToKCore ctx z
    ks <- termToKCore ctx s
    return $ KNif kz ks

  -- Lists
  Lst t       -> do
    kt <- termToKCore ctx t
    return $ KLst kt
  Nil         -> return KNil
  Con h t     -> do
    kh <- termToKCore ctx h
    kt <- termToKCore ctx t
    return $ KCon kh kt
  LstM n c    -> do
    kn <- termToKCore ctx n
    kc <- termToKCore ctx c
    return $ KMat kn kc

  -- Numbers
  Num _       -> return KU32
  Val v       -> case v of
    U64_V n   -> do
      let u32val = fromIntegral n :: Word32
      when (n > fromIntegral (maxBound :: Word32)) $
        trace ("Warning: U64 value " ++ show n ++ " truncated to U32") (return ())
      return $ KUva u32val
    I64_V n   -> do
      let u32val = fromIntegral n :: Word32
      trace ("Warning: I64 value " ++ show n ++ " converted to U32") $
        return $ KUva u32val
    CHR_V c   -> return $ KUva (fromIntegral (ord c))
    F64_V _   -> Left $ UnsupportedNumericType "F64"

  Op2 op a b  -> do
    ka <- termToKCore ctx a
    kb <- termToKCore ctx b
    return $ KPri (op2ToKOp op) [ka, kb]

  Op1 op a    -> Left $ UnsupportedConstruct $ "Unary operation: " ++ show op

  -- Pairs
  Sig t f     -> do
    kt <- termToKCore ctx t
    kf <- termToKCore ctx f
    return $ KSig kt kf
  Tup a b     -> do
    ka <- termToKCore ctx a
    kb <- termToKCore ctx b
    return $ KTup ka kb
  SigM f      -> do
    kf <- termToKCore ctx f
    return $ KGet kf

  -- Equality
  Eql t a b   -> do
    kt <- termToKCore ctx t
    ka <- termToKCore ctx a
    kb <- termToKCore ctx b
    return $ KEql kt ka kb
  Rfl         -> return KRfl
  EqlM f      -> do
    kf <- termToKCore ctx f
    -- EqlM is a match on equality, just apply the function
    return kf
  Rwt e f     -> do
    ke <- termToKCore ctx e
    kf <- termToKCore ctx f
    -- Simplified rewrite - KolmoC's rewrite takes 3 args: ~e:P;f
    -- We'll need to extract P from context or infer it
    return $ KRwt ke KSet kf  -- Using Set as placeholder for P

  -- Empty
  Emp         -> return KEmp
  EmpM        -> return KErf

  -- Primitives
  Pri p       -> return $ KPri (priToKPri p) []

  -- Logging (compile to identity)
  Log _ x     -> termToKCore ctx x

  -- Location (strip)
  Loc _ t     -> termToKCore ctx t

  -- Check and trust (strip)
  Chk v _     -> termToKCore ctx v
  Tst v       -> termToKCore ctx v

  -- Use (inline)
  Let _ _ v f -> do
    kv <- termToKCore ctx v
    kf <- termToKCore ctx (f v)
    return $ KApp (KLam "_" kf) kv
  Use _ v f   -> termToKCore ctx (f v)

  -- Unsupported constructs
  Pat _ _ _   -> Left $ PatternMatchNotDesugared "Pattern match should be desugared"
  IO _        -> Left $ IONotSupported "IO operations not supported"
  Met _ _ _   -> Left $ MetaVariableNotSupported "Meta variables not supported"
  Frk _ _ _   -> Left $ ForkNotSupported "Fork constructs not supported"

  -- Enums - compile to strings/symbols for now
  Enu _       -> return KSet  -- Enum type becomes Set
  Sym s       -> return $ KPri ("SYM:" ++ s) []
  EnuM _ _    -> Left $ UnsupportedConstruct "Enum match"

-- Helper to extract body from lambda with substitution
subst :: Core.Name -> (Term -> Term) -> Term
subst n f = f (Var n 0)

-- Convert string to 4-letter label
labToStr :: Term -> Lab
labToStr (Var n _) = take 4 (n ++ "____")
labToStr _ = "LABL"

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
op2ToKOp :: NOp2 -> String
op2ToKOp ADD = "ADD"
op2ToKOp SUB = "SUB"
op2ToKOp MUL = "MUL"
op2ToKOp DIV = "DIV"
op2ToKOp MOD = "MOD"
op2ToKOp EQL = "EQ"
op2ToKOp NEQ = "NEQ"
op2ToKOp LST = "LT"
op2ToKOp GRT = "GT"
op2ToKOp LEQ = "LEQ"
op2ToKOp GEQ = "GEQ"
op2ToKOp AND = "AND"
op2ToKOp OR  = "OR"
op2ToKOp XOR = "XOR"
op2ToKOp SHL = "SHL"
op2ToKOp SHR = "SHR"
op2ToKOp POW = "POW"

-- Convert NOp1 to KolmoC operation string
op1ToKOp :: NOp1 -> String
op1ToKOp NOT = "NOT"
op1ToKOp NEG = "NEG"

-- Convert PriF to KolmoC primitive string
priToKPri :: PriF -> String
priToKPri U64_TO_CHAR     = "U64_TO_CHAR"
priToKPri CHAR_TO_U64     = "CHAR_TO_U64"
priToKPri HVM_INC         = "INC"
priToKPri HVM_DEC         = "DEC"
priToKPri IO_PURE         = "IO_PURE"
priToKPri IO_BIND         = "IO_BIND"
priToKPri IO_PRINT        = "IO_PRINT"
priToKPri IO_PUTC         = "IO_PUTC"
priToKPri IO_GETC         = "IO_GETC"
priToKPri IO_READ_FILE    = "IO_READ_FILE"
priToKPri IO_WRITE_FILE   = "IO_WRITE_FILE"

-- Helper to remove location and check wrappers
cutTerm :: Term -> Term
cutTerm (Loc _ t) = cutTerm t
cutTerm (Chk x _) = cutTerm x
cutTerm t         = t