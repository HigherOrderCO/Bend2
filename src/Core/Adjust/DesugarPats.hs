{-# LANGUAGE ViewPatterns #-}

-- Pattern Desugaring
-- ==================
-- This module performs two steps:
-- 1. Specializes default cases by expanding them to cover all constructors explicitly
-- 2. Converts all Pats to native expression-based matches
--
-- Example of specialization:
--   match a: case @E{n,f}: @E{n,f} ; case v: v
-- becomes:
--   match a: case @E{n,f}: @E{n,f} ; case @F{h}: use v = @F{h}; v

module Core.Adjust.DesugarPats where

import Core.Bind
import Core.FreeVars
import Core.Show
import Core.Type
import Core.WHNF
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List (find, partition)
import Debug.Trace (trace)

-- | Main entry point: first specialize defaults, then desugar patterns
desugarPats :: Int -> Span -> Book -> Term -> Term
desugarPats d span book term = 
  let specialized = specializePats d book term
  in removePats d span book specialized

-- ============================================================================
-- STEP 1: Specialize default cases
-- ============================================================================

-- | Specialize all default cases in a term
specializePats :: Int -> Book -> Term -> Term
specializePats d book term = go d term where
  go d (Pat scruts moves cases) = 
    Pat scruts moves (specializePatCases d book scruts cases)
  go d (Loc s t) = Loc s (go d t)
  go d (Fix n f) = Fix n (\x -> go (d+1) (f x))
  go d (Let k t v f) = Let k (fmap (go d) t) (go d v) (\x -> go (d+1) (f x))
  go d (Use k v f) = Use k (go d v) (\x -> go (d+1) (f x))
  go d (Lam n t f) = Lam n (fmap (go d) t) (\x -> go (d+1) (f x))
  go d (App f x) = App (go d f) (go d x)
  go d (All a b) = All (go d a) (go d b)
  go d (Sig a b) = Sig (go d a) (go d b)
  go d (Tup a b) = Tup (go d a) (go d b)
  go d (Con h t) = Con (go d h) (go d t)
  go d (Suc n) = Suc (go d n)
  go d (Op2 o a b) = Op2 o (go d a) (go d b)
  go d (Op1 o a) = Op1 o (go d a)
  go d (Chk x t) = Chk (go d x) (go d t)
  go d (Tst x) = Tst (go d x)
  go d (UniM f) = UniM (go d f)
  go d (BitM f t) = BitM (go d f) (go d t)
  go d (NatM z s) = NatM (go d z) (go d s)
  go d (LstM n c) = LstM (go d n) (go d c)
  go d (EnuM cs e) = EnuM [(s, go d t) | (s, t) <- cs] (fmap (go d) e)
  go d (SigM f) = SigM (go d f)
  go d (EqlM f) = EqlM (go d f)
  go d (SupM l f) = SupM (go d l) (go d f)
  go d (Sup l a b) = Sup (go d l) (go d a) (go d b)
  go d (Eql t a b) = Eql (go d t) (go d a) (go d b)
  go d (Rwt e f) = Rwt (go d e) (go d f)
  go d (Frk l a b) = Frk (go d l) (go d a) (go d b)
  go d (Log s x) = Log (go d s) (go d x)
  go d (Met i t x) = Met i (go d t) (map (go d) x)
  go d t = t  -- All other terms remain unchanged

-- | Specialize cases in a pattern match
specializePatCases :: Int -> Book -> [Term] -> [Case] -> [Case]
specializePatCases d book [] cases = cases  -- No scrutinee, return as-is
specializePatCases d book (scrut:_) cases = 
  case findDefaultCase cases of
    Nothing -> cases  -- No default case, return as-is
    Just (defVar, defBody, otherCases) ->
      -- Try to infer type from scrutinee or existing cases
      case inferTypeFromCases book otherCases of
        Nothing -> cases  -- Can't infer type, return as-is
        Just typeName ->
          case getTypeConstructors book typeName of
            Nothing -> cases  -- Type not found, return as-is
            Just ctors ->
              let existingCtors = getExistingConstructors otherCases
                  missingCtors = filter (\(name, _) -> not (name `elem` existingCtors)) ctors
                  newCases = map (makeCase d defVar defBody) missingCtors
              in otherCases ++ newCases

-- | Find a default case (variable pattern) in the cases
findDefaultCase :: [Case] -> Maybe (String, Term, [Case])
findDefaultCase cases = go [] cases where
  go acc [] = Nothing
  go acc ((pats, body):rest) = 
    case pats of
      [pat] | isVarPattern pat -> 
        let varName = getVarName pat
        in Just (varName, body, acc ++ rest)
      _ -> go (acc ++ [(pats, body)]) rest
  
  isVarPattern (Var _ _) = True
  isVarPattern (Loc _ t) = isVarPattern t
  isVarPattern _ = False
  
  getVarName (Var n _) = n
  getVarName (Loc _ t) = getVarName t
  getVarName _ = error "getVarName: not a variable"

-- | Infer type name from existing constructor cases
inferTypeFromCases :: Book -> [Case] -> Maybe String
inferTypeFromCases book@(Book defs _ typeCtors) cases = 
  findTypeFromConstructor (getFirstConstructor cases)
  where
    getFirstConstructor [] = Nothing
    getFirstConstructor ((pats, _):rest) = 
      case pats of
        [pat] -> extractConstructor pat
        _ -> getFirstConstructor rest
    
    extractConstructor :: Term -> Maybe String
    extractConstructor term = case term of
      Tup (Sym s) _ -> Just s  -- Pattern like (@E, ...)
      Tup (Loc _ (Sym s)) _ -> Just s  -- Pattern like (Loc ... @E, ...)
      Sym s -> Just s          -- Simple enum constructor
      Loc _ t -> extractConstructor t
      _ -> Nothing
    
    findTypeFromConstructor :: Maybe String -> Maybe String
    findTypeFromConstructor Nothing = Nothing
    findTypeFromConstructor (Just ctorName) = 
      M.foldlWithKey findType Nothing typeCtors
      where
        findType acc typeName ctors =
          case acc of
            Just _ -> acc
            Nothing -> if any (\(cname, _) -> cname == ctorName) ctors
                      then Just typeName
                      else Nothing

-- | Get list of existing constructor names from cases
-- After flattening, patterns are single-level, so we can simply extract all constructors
getExistingConstructors :: [Case] -> [String]
getExistingConstructors cases = concatMap extractFromCase cases where
  extractFromCase :: Case -> [String]
  extractFromCase (pats, _) = case pats of
    [pat] -> maybeToList (extractConstructor pat)
    _ -> []
  
  extractConstructor :: Term -> Maybe String
  extractConstructor term = case term of
    Tup (Sym s) _ -> Just s
    Tup (Loc _ (Sym s)) _ -> Just s  -- Handle located symbols
    Sym s -> Just s  -- Simple enum constructor
    Loc _ t -> extractConstructor t
    _ -> Nothing
  
  maybeToList Nothing = []
  maybeToList (Just x) = [x]

-- | Get type constructors from the book
getTypeConstructors :: Book -> String -> Maybe [(String, Int)]
getTypeConstructors (Book _ _ typeCtors) typeName = M.lookup typeName typeCtors

-- | Create a new case for a missing constructor
makeCase :: Int -> String -> Term -> (String, Int) -> Case
makeCase d defVar defBody (ctorName, arity) = 
  let pat = makePattern d ctorName arity
      reconstructed = makeReconstruction d ctorName arity
      body = Use defVar reconstructed (\_ -> defBody)
  in ([pat], body)

-- | Create the reconstruction term for use binding
makeReconstruction :: Int -> String -> Int -> Term
makeReconstruction d ctorName 0 = 
  -- No fields: (&Ctor, ())
  Tup (Sym ctorName) One
makeReconstruction d ctorName arity = 
  -- With fields: (&Ctor, field1, field2, ..., ())
  Tup (Sym ctorName) (makeFieldVars d arity)
  where
    makeFieldVars d 1 = Tup (Var ("_f" ++ show d) d) One
    makeFieldVars d n = Tup (Var ("_f" ++ show d) d) (makeFieldVars (d+1) (n-1))

-- | Create a pattern for a constructor with given arity
makePattern :: Int -> String -> Int -> Term
makePattern d ctorName 0 = 
  -- No fields: (&Ctor, ())
  Tup (Sym ctorName) One
makePattern d ctorName arity = 
  -- With fields: (&Ctor, field1, field2, ..., ())
  Tup (Sym ctorName) (makeFields d arity)
  where
    makeFields d 1 = Tup (Var ("_f" ++ show d) d) One
    makeFields d n = Tup (Var ("_f" ++ show d) d) (makeFields (d+1) (n-1))

-- ============================================================================
-- STEP 2: Remove Pats and convert to native matches
-- ============================================================================

-- | Convert Pats to native expression-based matches
removePats :: Int -> Span -> Book -> Term -> Term
removePats d span book (Var n i)       = Var n i
removePats d span book (Ref n i)       = Ref n i
removePats d span book (Sub t)         = Sub (removePats d span book t)
removePats d span book (Fix n f)       = Fix n (\x -> removePats (d+1) span book (f x))
removePats d span book (Let k t v f)   = Let k (fmap (removePats d span book) t) (removePats d span book v) (\x -> removePats (d+1) span book (f x))
removePats d span book (Use k v f)     = Use k (removePats d span book v) (\x -> removePats (d+1) span book (f x))
removePats d span book Set             = Set
removePats d span book (Chk x t)       = Chk (removePats d span book x) (removePats d span book t)
removePats d span book (Tst x)         = Tst (removePats d span book x)
removePats d span book Emp             = Emp
removePats d span book EmpM            = EmpM
removePats d span book Uni             = Uni
removePats d span book One             = One
removePats d span book (UniM f)        = UniM (removePats d span book f)
removePats d span book Bit             = Bit
removePats d span book Bt0             = Bt0
removePats d span book Bt1             = Bt1
removePats d span book (BitM f t)      = BitM (removePats d span book f) (removePats d span book t)
removePats d span book Nat             = Nat
removePats d span book Zer             = Zer
removePats d span book (Suc n)         = Suc (removePats d span book n)
removePats d span book (NatM z s)      = NatM (removePats d span book z) (removePats d span book s)
removePats d span book (Lst t)         = Lst (removePats d span book t)
removePats d span book Nil             = Nil
removePats d span book (Con h t)       = Con (removePats d span book h) (removePats d span book t)
removePats d span book (LstM n c)      = LstM (removePats d span book n) (removePats d span book c)
removePats d span book (Enu s)         = Enu s
removePats d span book (Sym s)         = Sym s
removePats d span book (EnuM c e)      = EnuM [(s, removePats d span book t) | (s, t) <- c] (fmap (removePats d span book) e)
removePats d span book (Sig a b)       = Sig (removePats d span book a) (removePats d span book b)
removePats d span book (Tup a b)       = Tup (removePats d span book a) (removePats d span book b)
removePats d span book (SigM f)        = SigM (removePats d span book f)
removePats d span book (All a b)       = All (removePats d span book a) (removePats d span book b)
removePats d span book (Lam n t f)     = Lam n (fmap (removePats d span book) t) (\x -> removePats (d+1) span book (f x))
removePats d span book (App f x)       = App (removePats d span book f) (removePats d span book x)
removePats d span book (Eql t a b)     = Eql (removePats d span book t) (removePats d span book a) (removePats d span book b)
removePats d span book Rfl             = Rfl
removePats d span book (EqlM f)        = EqlM (removePats d span book f)
removePats d span book (Met i t x)     = Met i (removePats d span book t) (map (removePats d span book) x)
removePats d span book Era             = Era
removePats d span book (Sup l a b)     = Sup (removePats d span book l) (removePats d span book a) (removePats d span book b)
removePats d span book (SupM l f)      = SupM (removePats d span book l) (removePats d span book f)
removePats d span book (Frk l a b)     = Frk (removePats d span book l) (removePats d span book a) (removePats d span book b)
removePats d span book (Rwt e f)       = Rwt (removePats d span book e) (removePats d span book f)
removePats d span book (Num t)         = Num t
removePats d span book (Val v)         = Val v
removePats d span book (Op2 o a b)     = Op2 o (removePats d span book a) (removePats d span book b)
removePats d span book (Op1 o a)       = Op1 o (removePats d span book a)
removePats d span book (Pri p)         = Pri p
removePats d span book (Log s x)       = Log (removePats d span book s) (removePats d span book x)
removePats d span book (Loc s t)       = Loc s (removePats d s book t)
removePats d span book (Pat [s] ms cs) = match d span book s ms cs
removePats d span book (Pat ss  ms []) = One
removePats d span book (Pat ss  ms cs) = errorWithSpan span "Invalid pattern: multiple scrutinees after flattening"

match :: Int -> Span -> Book -> Term -> [Move] -> [Case] -> Term

-- match x { 0n: z ; 1n+p: s }
-- ---------------------------
-- ~x { 0n: z ; 1n+: λp. s }
match d span book x ms (([(cut -> Zer)], z) : ([(cut -> Suc p)], s) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ removePats d span book z
        if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) $ removePats (d+1) span book s

-- match x { 1n+p: s ; 0n: z }
-- ---------------------------
-- ~x { 0n: z ; 1n+: λp. s }
match d span book x ms (([(cut -> Suc p)], s) : ([(cut -> Zer)], z) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ removePats d span book z
        if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) $ removePats (d+1) span book s

-- match x { 0n: z ; k: v }
-- --------------------------------------
-- ~x { 0n: z ; 1n+: λk. v[k := 1n+k] }
match d span book x ms (([(cut -> Zer)], z) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ desugarPats d span book z
        if_suc = Lam k (Just Nat) $ \x -> lam d (map fst ms) $ removePats (d+1) span book (bindVarByName k (Suc (Var k 0)) v)

-- match x { 1n+p: s ; k: v }
-- ------------------------------------
-- ~x { 0n: v[k := 0n] ; 1n+: λp. s }
match d span book x ms (([(cut -> Suc p)], s) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ removePats d span book (bindVarByName k Zer v)
        if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) $ desugarPats (d+1) span book s

-- match x { False: f ; True: t }
-- ------------------------------
-- ~x { False: f ; True: t }
match d span book x ms (([(cut -> Bt0)], f) : ([(cut -> Bt1)], t) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ removePats d span book f) (lam d (map fst ms) $ removePats d span book t)) x

-- match x { True: t ; False: f }
-- ------------------------------
-- ~x { False: f ; True: t }
match d span book x ms (([(cut -> Bt1)], t) : ([(cut -> Bt0)], f) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ removePats d span book f) (lam d (map fst ms) $ removePats d span book t)) x

-- match x { False: f ; k: v }
-- --------------------------------------
-- ~x { False: f ; True: v[k := True] }
match d span book x ms (([(cut -> Bt0)], f) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ removePats d span book f) (lam d (map fst ms) $ removePats d span book (bindVarByName k Bt1 v))) x

-- match x { True: t ; k: v }
-- ---------------------------------------
-- ~x { False: v[k := False] ; True: t }
match d span book x ms (([(cut -> Bt1)], t) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ removePats d span book (bindVarByName k Bt0 v)) (lam d (map fst ms) $ removePats d span book t)) x

-- match x { []: n ; h<>t: c }
-- ------------------------------
-- ~x { []: n ; <>: λh. λt. c }
match d span book x ms (([(cut -> Nil)], n) : ([(cut -> Con h t)], c) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ removePats d span book n
        if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) $ removePats (d+2) span book c

-- match x { h<>t: c ; []: n }
-- ------------------------------
-- ~x { []: n ; <>: λh. λt. c }
match d span book x ms (([(cut -> Con h t)], c) : ([(cut -> Nil)], n) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ removePats d span book n
        if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) $ removePats (d+2) span book c

-- match x { []: n ; k: v }
-- -----------------------------------------
-- ~x { []: n ; <>: λh. λt. v[k := h<>t] }
match d span book x ms (([(cut -> Nil)], n) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ removePats d span book n
        if_con = Lam (nam d) Nothing $ \_ -> Lam (nam (d+1)) Nothing $ \_ -> lam d (map fst ms) $ removePats (d+2) span book (bindVarByName k (Con (var d) (var (d+1))) v)

-- match x { h<>t: c ; k: v }
-- ---------------------------------------
-- ~x { []: v[k := []] ; <>: λh. λt. c }
match d span book x ms (([(cut -> Con h t)], c) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ removePats d span book (bindVarByName k Nil v)
        if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) $ removePats (d+2) span book c

-- match x { (): u }
-- -----------------
-- ~x { (): u }
-- Preserve location from the unit pattern: if the case pattern is a located
-- '()', then the generated λ{(): ...} inherits that original location.
match d span book x ms (([p], u) : _) | isUnitPat p =
  let mloc = unitPatLoc p in
  let body = lam d (map fst ms) $ removePats d span book u in
  let uni  = maybe (UniM body) (\sp -> Loc sp (UniM body)) mloc in
  apps d (map snd ms) $ App uni x
  where
    isUnitPat :: Term -> Bool
    isUnitPat (cut -> One) = True
    isUnitPat _            = False
    unitPatLoc :: Term -> Maybe Span
    unitPatLoc (Loc sp (cut -> One)) = Just sp
    unitPatLoc _                         = Nothing

-- match x { (a,b): p }
-- --------------------
-- ~x { (,): λa. λb. p }
-- Preserve location for tuple patterns
match d span book x ms (([tup], p) : _) | isTupPat tup =
  let mloc = tupPatLoc tup in
  let (a, b) = tupPatFields tup in
  let if_tup = Lam (patOf d a) Nothing $ \_ -> Lam (patOf (d+1) b) Nothing $ \_ -> lam d (map fst ms) $ removePats (d+2) span book p in
  let sigm = maybe (SigM if_tup) (\sp -> Loc sp (SigM if_tup)) mloc in
  apps d (map snd ms) $ App sigm x
  where
    isTupPat :: Term -> Bool
    isTupPat (cut -> Tup _ _) = True
    isTupPat _ = False
    tupPatLoc :: Term -> Maybe Span
    tupPatLoc (Loc sp (cut -> Tup _ _)) = Just sp
    tupPatLoc _ = Nothing
    tupPatFields :: Term -> (Term, Term)
    tupPatFields (cut -> Tup a b) = (a, b)
    tupPatFields (Loc _ (cut -> Tup a b)) = (a, b)
    tupPatFields _ = error "tupPatFields: not a tuple"

-- match x { @S1: b1 ; @S2: b2 ; ... ; k: d }
-- ------------------------------------------
-- ~x { @S1:b1 ; @S2:b2 ; ... ; default: λk. d }
match d span book x ms cs@(([(cut -> Sym _)], _) : _) =
  let (cBranches, defBranch) = collect cs
      enumMatch = case span of
        Span (0,0) (0,0) _ _ -> EnuM cBranches defBranch
        _                    -> Loc span (EnuM cBranches defBranch)
  in apps d (map snd ms) $ App enumMatch x
  where
    collect :: [Case] -> ([(String, Term)], Maybe Term)
    collect [] = ([], Nothing)
    collect (([(cut -> Sym s)], rhs) : rest) =
      let (cs, def) = collect rest
      in ((s, lam d (map fst ms) $ removePats d span book rhs) : cs, def)
    collect (([(cut -> Var k _)], rhs) : _) =
      ([], Just $ Lam k Nothing $ \_ -> lam d (map fst ms) $ removePats (d+1) span book rhs)
    collect (c:_) = errorWithSpan span "Invalid pattern: invalid Sym case"

-- match x { &L{a,b}: s }
-- ---------------------------
-- ~ x { &L{,}: λa. λb. s }
match d span book x ms (([(cut -> Sup l a b)], s) : _) =
  apps d (map snd ms) $ App (SupM l if_sup) x
  where if_sup = Lam (patOf d a) Nothing $ \_ -> Lam (patOf (d+1) b) Nothing $ \_ -> lam d (map fst ms) $ removePats (d+2) span book s

-- match x { Rfl: r }
-- ------------------
-- ~x { Rfl: r }
match d span book x ms (([(cut -> Rfl)], r) : _) =
  apps d (map snd ms) $ App (EqlM (lam d (map fst ms) $ removePats d span book r)) x

-- match x { k: body }
-- -------------------
-- body[k := x]
match d span book x ms (([(cut -> Var k i)], body) : _) =
  lam d (map fst ms) $ removePats d span book (shove d ((k, x) : ms) body)

-- match x { }
-- -----------
-- λ{}
match d span book x ms [] =
  apps d (map snd ms) (App EmpM x)

-- Invalid pattern
-- match d span s ms cs = error $ "match - invalid pattern: " ++ show (d, s, ms, cs) ++ "\n" ++ show span
match d span book s ms cs = errorWithSpan span "Invalid pattern."

-- Helper function to create lambda abstractions
lam :: Int -> [Name] -> Term -> Term
lam d ks t = t
-- lam d []     t = t
-- lam d (k:ks) t = Lam k Nothing $ \_ -> lam (d+1) ks t

-- Applies n arguments to a value
apps :: Int -> [Term] -> Term -> Term
apps d ms t = t
-- apps d ms t = foldl (\t x -> App t x) t ms

-- Substitutes a move list into an expression
shove :: Int -> [Move] -> Term -> Term
shove d ms term = foldr (\ (k,v) x -> bindVarByName k v x) term ms

-- Creates a fresh name at given depth
nam :: Int -> String
nam d = "_x" ++ show d

-- Creates a fresh variable at given depth
var :: Int -> Term
var d = Var (nam d) d

-- Gets a var name, or creates a fresh one
patOf :: Int -> Term -> String
patOf d (cut->Var k i) = k
patOf d p              = nam d
