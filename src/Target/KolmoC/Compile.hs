{-# LANGUAGE ViewPatterns #-}

module Target.KolmoC.Compile where

import Control.Monad (forM, foldM, unless, when)
import Data.Char (isAlphaNum, ord, toUpper)
import Data.List (find)
import Data.Word (Word32)
import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace

import Core.Type hiding (Name)
import qualified Core.Type as Core
import Target.KolmoC.Type

-- Main compilation entry point
compileBook :: Book -> String -> Either KCompileError (KBook, Nick)
compileBook book@(Book defs _) mainFQN = do
  -- Pre-scan to collect all metavariable names
  let metas = S.fromList [name | (name, (_, term, _)) <- M.toList defs, isMet (cut term)]
  let ctx = CompileCtx book M.empty 0 [] metas False
  -- Check main exists
  unless (M.member mainFQN defs) $
    Left $ UnknownReference $ "Main function not found: " ++ mainFQN
  -- Compile all definitions
  finalCtx <- foldM compileDefn ctx (M.toList defs)
  -- Get main nick
  let mainNick = toNick mainFQN
  return (ctxDefs finalCtx, mainNick)
  where
    isMet (Met _ _ _) = True
    isMet _           = False

-- Compile a single definition
compileDefn :: CompileCtx -> (Core.Name, Defn) -> Either KCompileError CompileCtx
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
  kbody <- termToKCore ctx term
  let kbodyWithDup = autoDup kbody  -- Apply autodup pass
  ktype <- if isMeta
    then return Nothing  -- Generators have types in their declaration, not definition
    else Just <$> termToKCore ctx typ  -- Compile type for regular defs and asserts
  let kdef = KDefn nick ktype kbodyWithDup
  -- Add to metas set if it's a metavariable
  let updatedMetas = if isMeta then S.insert name (ctxMetas ctx) else ctxMetas ctx
  let updatedCtx = ctx { ctxDefs = M.insert nick kdef (ctxDefs ctx)
                       , ctxMetas = updatedMetas }
  return updatedCtx

-- Convert Bend Term to KolmoC Core
termToKCore :: CompileCtx -> Term -> Either KCompileError KCore
termToKCore ctx term = case cut term of
  -- Variables and references
  Var n _     -> return $ KVar n
  Ref k _     ->
    -- If k is a metavariable, use uppercase nick (unless inside Eql)
    let nick = toNick k
        isMeta = S.member k (ctxMetas ctx)
        shouldUppercase = isMeta && not (ctxInEql ctx)
        finalNick = if shouldUppercase then map toUpper nick else nick
    in return $ KRef finalNick
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
  SupM l f    -> case cut f of
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
    -- Inside Eql, use lowercase refs for metavariables (for generator tests)
    let ctxInEql = ctx { ctxInEql = True }
    kt <- termToKCore ctxInEql t
    ka <- termToKCore ctxInEql a
    kb <- termToKCore ctxInEql b
    return $ KEql kt ka kb
  Rfl         -> return KRfl
  EqlM f      -> do
    kf <- termToKCore ctx f
    -- EqlM is a match on equality, just apply the function
    return kf
  -- Rewrite: Bend's `rewrite e f` where e : T{a==b}
  -- At runtime, KolmoC erases rewrites: ~e:P;f → f
  -- The motive P is implicit in Bend (derived from the goal during type checking)
  -- Since we don't have access to the goal here, and KolmoC erases rewrites anyway,
  -- we just compile to the body f directly. This is semantically correct.
  Rwt e f     -> termToKCore ctx f

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
  -- Metavariables/Generators
  Met name typ metCtx -> do
    -- Compile the type signature
    ktyp <- termToKCore ctx typ
    -- Build context list from references
    kctx <- compileMetContext ctx metCtx
    -- Get metavariable nick
    let nick = toNick name
    -- Create GEN term with default seed 0
    return $ KGen nick kctx ktyp (KUva 0)
  Frk _ _ _   -> Left $ ForkNotSupported "Fork constructs not supported"

  -- Enums - compile to strings/symbols for now
  Enu _       -> return KSet  -- Enum type becomes Set
  Sym s       -> return $ KPri ("SYM:" ++ s) []
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

-- Metavariable context compilation
-- Compile Met context: [Term] -> List of (Var, TypeRef) pairs
compileMetContext :: CompileCtx -> [Term] -> Either KCompileError KCore
compileMetContext ctx terms = buildList terms
  where
    buildList [] = return KNil
    buildList (t:ts) = do
      rest <- buildList ts
      pair <- termToContextPair ctx t
      return $ KCon pair rest

-- Convert a single context term to (var, typeref) pair
termToContextPair :: CompileCtx -> Term -> Either KCompileError KCore
termToContextPair ctx term = case cut term of
  Ref k _ -> do
    -- Get the reference name and create tuple: #(var, @:ref)
    let refNick = toNick k
    let varName = refNick  -- Use ref name as variable
    return $ KTup (KVar varName) (KTyp refNick)

  _ -> Left $ UnsupportedConstruct
    "Metavariable context term must be a reference (expected Ref)"

-- ============================================================================
-- AUTODUP: Automatic DUP insertion for non-linear variable usage
-- ============================================================================

-- Main autodup pass - recursively process KCore and insert DUPs for non-linear vars
autoDup :: KCore -> KCore
autoDup term = case term of
  -- Lambda: check if variable is used multiple times
  KLam name body ->
    let processedBody = autoDup body  -- Recursively process body first
        count = countUsage name processedBody
    in if count <= 1
       then KLam name processedBody
       else KLam name (insertDupChain name count processedBody)

  -- Recursively process all other constructors
  KApp f x     -> KApp (autoDup f) (autoDup x)
  KAll t b     -> KAll (autoDup t) (autoDup b)
  KSup l a b   -> KSup l (autoDup a) (autoDup b)
  KDup l x y v b -> KDup l x y (autoDup v) (autoDup b)
  KUse u       -> KUse (autoDup u)
  KBif f t     -> KBif (autoDup f) (autoDup t)
  KNif z s     -> KNif (autoDup z) (autoDup s)
  KUif z s     -> KUif (autoDup z) (autoDup s)
  KCon h t     -> KCon (autoDup h) (autoDup t)
  KMat n c     -> KMat (autoDup n) (autoDup c)
  KEql t a b   -> KEql (autoDup t) (autoDup a) (autoDup b)
  KRwt e p f   -> KRwt (autoDup e) (autoDup p) (autoDup f)
  KSig t f     -> KSig (autoDup t) (autoDup f)
  KTup a b     -> KTup (autoDup a) (autoDup b)
  KGet p       -> KGet (autoDup p)
  KSuc n       -> KSuc (autoDup n)
  KInc n       -> KInc (autoDup n)
  KLst t       -> KLst (autoDup t)
  KSpn n x     -> KSpn n (autoDup x)
  KPri op args -> KPri op (map autoDup args)
  KGen n c t s -> KGen n (autoDup c) (autoDup t) (autoDup s)

  -- Atoms (no recursion needed)
  _ -> term

-- Count how many times a variable is used (respecting shadowing)
countUsage :: Nick -> KCore -> Int
countUsage var term = case term of
  KVar n | n == var -> 1
         | otherwise -> 0
  KDP0 _ n | n == var -> 1
           | otherwise -> 0
  KDP1 _ n | n == var -> 1
           | otherwise -> 0

  -- Lambda shadows the variable if names match
  KLam n body | n == var -> 0
              | otherwise -> countUsage var body

  -- Recursively count in compound terms
  KApp f x     -> countUsage var f + countUsage var x
  KAll t b     -> countUsage var t + countUsage var b
  KSup _ a b   -> countUsage var a + countUsage var b
  KDup _ x y v b -> countUsage var v + countUsage var b
  KUse u       -> countUsage var u
  KBif f t     -> countUsage var f + countUsage var t
  KNif z s     -> countUsage var z + countUsage var s
  KUif z s     -> countUsage var z + countUsage var s
  KCon h t     -> countUsage var h + countUsage var t
  KMat n c     -> countUsage var n + countUsage var c
  KEql t a b   -> countUsage var t + countUsage var a + countUsage var b
  KRwt e p f   -> countUsage var e + countUsage var p + countUsage var f
  KSig t f     -> countUsage var t + countUsage var f
  KTup a b     -> countUsage var a + countUsage var b
  KGet p       -> countUsage var p
  KSuc n       -> countUsage var n
  KInc n       -> countUsage var n
  KLst t       -> countUsage var t
  KSpn _ x     -> countUsage var x
  KPri _ args  -> sum (map (countUsage var) args)
  KGen _ c t s -> countUsage var c + countUsage var t + countUsage var s

  -- Atoms don't contain variables
  _ -> 0

-- Insert DUP chain for a variable used N times (N >= 2)
-- Pattern: !D1_v&v = v; !D2_v&v = D1_v₁; ... ; body[v₁→D1_v₀, v₂→D2_v₀, ..., vₙ→Dₙ₋₁₁]
insertDupChain :: Nick -> Int -> KCore -> KCore
insertDupChain var count body =
  let dupNames = ["D" ++ show i ++ "_" ++ var | i <- [1..count-1]]
      bodyWithSubst = substituteOccurrences var dupNames body 0
  in wrapDups var dupNames bodyWithSubst

-- Wrap body with DUP chain
-- For dupNames = [D1_a, D2_a], generates:
--   !D1_a&a = a; !D2_a&a = D1_a₁; body
wrapDups :: Nick -> [Nick] -> KCore -> KCore
wrapDups _ [] body = body
wrapDups var [d1] body =
  KDup var d1 "_" (KVar var) body
wrapDups var (d1:rest) body =
  KDup var d1 "_" (KVar var) (wrapDups' var d1 rest body)
  where
    wrapDups' _ _ [] b = b
    wrapDups' v prev (d:ds) b =
      KDup v d "_" (KDP1 v prev) (wrapDups' v d ds b)

-- Substitute occurrences of variable with DP0/DP1 references
-- occurrence i → Di₀, final occurrence → Dₙ₋₁₁
substituteOccurrences :: Nick -> [Nick] -> KCore -> Int -> KCore
substituteOccurrences var dupNames body occNum =
  fst $ subst var dupNames body occNum
  where
    subst v dups term n = case term of
      KVar name | name == v ->
        let dupIdx = n
            ref = if dupIdx < length dups
                  then KDP0 v (dups !! dupIdx)
                  else KDP1 v (last dups)
        in (ref, n + 1)
      KVar name -> (KVar name, n)

      KDP0 l name -> (KDP0 l name, n)
      KDP1 l name -> (KDP1 l name, n)

      -- Lambda shadows if names match
      KLam name lamBody | name == v -> (KLam name lamBody, n)
                        | otherwise ->
        let (substBody, nextN) = subst v dups lamBody n
        in (KLam name substBody, nextN)

      -- Recursively substitute in compound terms
      KApp f x ->
        let (substF, n1) = subst v dups f n
            (substX, n2) = subst v dups x n1
        in (KApp substF substX, n2)

      KAll t b ->
        let (substT, n1) = subst v dups t n
            (substB, n2) = subst v dups b n1
        in (KAll substT substB, n2)

      KSup l a b ->
        let (substA, n1) = subst v dups a n
            (substB, n2) = subst v dups b n1
        in (KSup l substA substB, n2)

      KDup l x y val dupBody ->
        let (substVal, n1) = subst v dups val n
            (substDupBody, n2) = subst v dups dupBody n1
        in (KDup l x y substVal substDupBody, n2)

      KUse u ->
        let (substU, n1) = subst v dups u n
        in (KUse substU, n1)

      KBif f t ->
        let (substF, n1) = subst v dups f n
            (substT, n2) = subst v dups t n1
        in (KBif substF substT, n2)

      KNif z s ->
        let (substZ, n1) = subst v dups z n
            (substS, n2) = subst v dups s n1
        in (KNif substZ substS, n2)

      KUif z s ->
        let (substZ, n1) = subst v dups z n
            (substS, n2) = subst v dups s n1
        in (KUif substZ substS, n2)

      KCon h t ->
        let (substH, n1) = subst v dups h n
            (substT, n2) = subst v dups t n1
        in (KCon substH substT, n2)

      KMat m c ->
        let (substM, n1) = subst v dups m n
            (substC, n2) = subst v dups c n1
        in (KMat substM substC, n2)

      KEql t a b ->
        let (substT, n1) = subst v dups t n
            (substA, n2) = subst v dups a n1
            (substB, n3) = subst v dups b n2
        in (KEql substT substA substB, n3)

      KRwt e p f ->
        let (substE, n1) = subst v dups e n
            (substP, n2) = subst v dups p n1
            (substF, n3) = subst v dups f n2
        in (KRwt substE substP substF, n3)

      KSig t f ->
        let (substT, n1) = subst v dups t n
            (substF, n2) = subst v dups f n1
        in (KSig substT substF, n2)

      KTup a b ->
        let (substA, n1) = subst v dups a n
            (substB, n2) = subst v dups b n1
        in (KTup substA substB, n2)

      KGet p ->
        let (substP, n1) = subst v dups p n
        in (KGet substP, n1)

      KSuc s ->
        let (substS, n1) = subst v dups s n
        in (KSuc substS, n1)

      KInc i ->
        let (substI, n1) = subst v dups i n
        in (KInc substI, n1)

      KLst t ->
        let (substT, n1) = subst v dups t n
        in (KLst substT, n1)

      KSpn name x ->
        let (substX, n1) = subst v dups x n
        in (KSpn name substX, n1)

      KPri op args ->
        let (substArgs, nextN) = substList v dups args n
        in (KPri op substArgs, nextN)

      KGen name c t s ->
        let (substC, n1) = subst v dups c n
            (substT, n2) = subst v dups t n1
            (substS, n3) = subst v dups s n2
        in (KGen name substC substT substS, n3)

      -- Atoms
      _ -> (term, n)

    substList _ _ [] n = ([], n)
    substList v dups (x:xs) n =
      let (substX, n1) = subst v dups x n
          (substXs, n2) = substList v dups xs n1
      in (substX:substXs, n2)

