{-# LANGUAGE ViewPatterns #-}

-- Pattern Desugaring and Default Specialization
-- ==============================================
-- This module handles two closely related transformations:
-- 1. Converts all Pats to native expression-based matches (desugarPats)
-- 2. Specializes default cases in enum matches to explicit constructors (specializeDefaults)

module Core.Adjust.DesugarPats where

import Core.Bind
import Core.Show
import Core.Type
import Core.WHNF
import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace (trace)

-- Public API
-- ----------

-- Combined transformation that desugars patterns then specializes defaults
desugarAndSpecialize :: Int -> Span -> Book -> Term -> Term
desugarAndSpecialize d span book term = 
  let desugared = desugarPatsCore d span book term
      specialized = specializeDefaultsCore d book desugared
  in specialized

-- Original individual APIs (kept for compatibility)
desugarPats :: Int -> Span -> Book -> Term -> Term
desugarPats = desugarAndSpecialize

-- Pattern Desugaring
-- ------------------

desugarPatsCore :: Int -> Span -> Book -> Term -> Term
desugarPatsCore d span book (Var n i)       = Var n i
desugarPatsCore d span book (Ref n i)       = Ref n i
desugarPatsCore d span book (Sub t)         = Sub (desugarPatsCore d span book t)
desugarPatsCore d span book (Fix n f)       = Fix n (\x -> desugarPatsCore (d+1) span book (f x))
desugarPatsCore d span book (Let k t v f)   = Let k (fmap (desugarPatsCore d span book) t) (desugarPatsCore d span book v) (\x -> desugarPatsCore (d+1) span book (f x))
desugarPatsCore d span book (Use k v f)     = Use k (desugarPatsCore d span book v) (\x -> desugarPatsCore (d+1) span book (f x))
desugarPatsCore d span book Set             = Set
desugarPatsCore d span book (Chk x t)       = Chk (desugarPatsCore d span book x) (desugarPatsCore d span book t)
desugarPatsCore d span book (Tst x)         = Tst (desugarPatsCore d span book x)
desugarPatsCore d span book Emp             = Emp
desugarPatsCore d span book EmpM            = EmpM
desugarPatsCore d span book Uni             = Uni
desugarPatsCore d span book One             = One
desugarPatsCore d span book (UniM f)        = UniM (desugarPatsCore d span book f)
desugarPatsCore d span book Bit             = Bit
desugarPatsCore d span book Bt0             = Bt0
desugarPatsCore d span book Bt1             = Bt1
desugarPatsCore d span book (BitM f t)      = BitM (desugarPatsCore d span book f) (desugarPatsCore d span book t)
desugarPatsCore d span book Nat             = Nat
desugarPatsCore d span book Zer             = Zer
desugarPatsCore d span book (Suc n)         = Suc (desugarPatsCore d span book n)
desugarPatsCore d span book (NatM z s)      = NatM (desugarPatsCore d span book z) (desugarPatsCore d span book s)
desugarPatsCore d span book (Lst t)         = Lst (desugarPatsCore d span book t)
desugarPatsCore d span book Nil             = Nil
desugarPatsCore d span book (Con h t)       = Con (desugarPatsCore d span book h) (desugarPatsCore d span book t)
desugarPatsCore d span book (LstM n c)      = LstM (desugarPatsCore d span book n) (desugarPatsCore d span book c)
desugarPatsCore d span book (Enu s)         = Enu s
desugarPatsCore d span book (Sym s)         = Sym s
desugarPatsCore d span book (EnuM c e)      = EnuM [(s, desugarPatsCore d span book t) | (s, t) <- c] (fmap (desugarPatsCore d span book) e)
desugarPatsCore d span book (Sig a b)       = Sig (desugarPatsCore d span book a) (desugarPatsCore d span book b)
desugarPatsCore d span book (Tup a b)       = Tup (desugarPatsCore d span book a) (desugarPatsCore d span book b)
desugarPatsCore d span book (SigM f)        = SigM (desugarPatsCore d span book f)
desugarPatsCore d span book (All a b)       = All (desugarPatsCore d span book a) (desugarPatsCore d span book b)
desugarPatsCore d span book (Lam n t f)     = Lam n (fmap (desugarPatsCore d span book) t) (\x -> desugarPatsCore (d+1) span book (f x))
desugarPatsCore d span book (App f x)       = App (desugarPatsCore d span book f) (desugarPatsCore d span book x)
desugarPatsCore d span book (Eql t a b)     = Eql (desugarPatsCore d span book t) (desugarPatsCore d span book a) (desugarPatsCore d span book b)
desugarPatsCore d span book Rfl             = Rfl
desugarPatsCore d span book (EqlM f)        = EqlM (desugarPatsCore d span book f)
desugarPatsCore d span book (Met i t x)     = Met i (desugarPatsCore d span book t) (map (desugarPatsCore d span book) x)
desugarPatsCore d span book Era             = Era
desugarPatsCore d span book (Sup l a b)     = Sup (desugarPatsCore d span book l) (desugarPatsCore d span book a) (desugarPatsCore d span book b)
desugarPatsCore d span book (SupM l f)      = SupM (desugarPatsCore d span book l) (desugarPatsCore d span book f)
desugarPatsCore d span book (Frk l a b)     = Frk (desugarPatsCore d span book l) (desugarPatsCore d span book a) (desugarPatsCore d span book b)
desugarPatsCore d span book (Rwt e f)       = Rwt (desugarPatsCore d span book e) (desugarPatsCore d span book f)
desugarPatsCore d span book (Num t)         = Num t
desugarPatsCore d span book (Val v)         = Val v
desugarPatsCore d span book (Op2 o a b)     = Op2 o (desugarPatsCore d span book a) (desugarPatsCore d span book b)
desugarPatsCore d span book (Op1 o a)       = Op1 o (desugarPatsCore d span book a)
desugarPatsCore d span book (Pri p)         = Pri p
desugarPatsCore d span book (Log s x)       = Log (desugarPatsCore d span book s) (desugarPatsCore d span book x)
desugarPatsCore d span book (Loc s t)       = Loc s (desugarPatsCore d s book t)
desugarPatsCore d span book (Pat [s] ms cs) = match d span book s ms cs
desugarPatsCore d span book (Pat ss  ms []) = One
desugarPatsCore d span book (Pat ss  ms cs) = errorWithSpan span "Invalid pattern: multiple scrutinees after flattening"

match :: Int -> Span -> Book -> Term -> [Move] -> [Case] -> Term

-- match x { 0n: z ; 1n+p: s }
-- ---------------------------
-- ~x { 0n: z ; 1n+: λp. s }
match d span book x ms (([(cut -> Zer)], z) : ([(cut -> Suc p)], s) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ desugarPatsCore d span book z
        if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) $ desugarPatsCore (d+1) span book s

-- match x { 1n+p: s ; 0n: z }
-- ---------------------------
-- ~x { 0n: z ; 1n+: λp. s }
match d span book x ms (([(cut -> Suc p)], s) : ([(cut -> Zer)], z) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ desugarPatsCore d span book z
        if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) $ desugarPatsCore (d+1) span book s

-- match x { 0n: z ; k: v }
-- --------------------------------------
-- ~x { 0n: z ; 1n+: λk. v[k := 1n+k] }
match d span book x ms (([(cut -> Zer)], z) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ desugarPatsCore d span book z
        if_suc = Lam k (Just Nat) $ \x -> lam d (map fst ms) $ desugarPatsCore (d+1) span book (bindVarByName k (Suc (Var k 0)) v)

-- match x { 1n+p: s ; k: v }
-- ------------------------------------
-- ~x { 0n: v[k := 0n] ; 1n+: λp. s }
match d span book x ms (([(cut -> Suc p)], s) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ desugarPatsCore d span book (bindVarByName k Zer v)
        if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) $ desugarPatsCore (d+1) span book s

-- match x { False: f ; True: t }
-- ------------------------------
-- ~x { False: f ; True: t }
match d span book x ms (([(cut -> Bt0)], f) : ([(cut -> Bt1)], t) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ desugarPatsCore d span book f) (lam d (map fst ms) $ desugarPatsCore d span book t)) x

-- match x { True: t ; False: f }
-- ------------------------------
-- ~x { False: f ; True: t }
match d span book x ms (([(cut -> Bt1)], t) : ([(cut -> Bt0)], f) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ desugarPatsCore d span book f) (lam d (map fst ms) $ desugarPatsCore d span book t)) x

-- match x { False: f ; k: v }
-- --------------------------------------
-- ~x { False: f ; True: v[k := True] }
match d span book x ms (([(cut -> Bt0)], f) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ desugarPatsCore d span book f) (lam d (map fst ms) $ desugarPatsCore d span book (bindVarByName k Bt1 v))) x

-- match x { True: t ; k: v }
-- ---------------------------------------
-- ~x { False: v[k := False] ; True: t }
match d span book x ms (([(cut -> Bt1)], t) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ desugarPatsCore d span book (bindVarByName k Bt0 v)) (lam d (map fst ms) $ desugarPatsCore d span book t)) x

-- match x { []: n ; h<>t: c }
-- ------------------------------
-- ~x { []: n ; <>: λh. λt. c }
match d span book x ms (([(cut -> Nil)], n) : ([(cut -> Con h t)], c) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ desugarPatsCore d span book n
        if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) $ desugarPatsCore (d+2) span book c

-- match x { h<>t: c ; []: n }
-- ------------------------------
-- ~x { []: n ; <>: λh. λt. c }
match d span book x ms (([(cut -> Con h t)], c) : ([(cut -> Nil)], n) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ desugarPatsCore d span book n
        if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) $ desugarPatsCore (d+2) span book c

-- match x { []: n ; k: v }
-- -----------------------------------------
-- ~x { []: n ; <>: λh. λt. v[k := h<>t] }
match d span book x ms (([(cut -> Nil)], n) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ desugarPatsCore d span book n
        if_con = Lam (nam d) Nothing $ \_ -> Lam (nam (d+1)) Nothing $ \_ -> lam d (map fst ms) $ desugarPatsCore (d+2) span book (bindVarByName k (Con (var d) (var (d+1))) v)

-- match x { h<>t: c ; k: v }
-- ---------------------------------------
-- ~x { []: v[k := []] ; <>: λh. λt. c }
match d span book x ms (([(cut -> Con h t)], c) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ desugarPatsCore d span book (bindVarByName k Nil v)
        if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) $ desugarPatsCore (d+2) span book c

-- match x { (): u }
-- -----------------
-- ~x { (): u }
-- Preserve location from the unit pattern: if the case pattern is a located
-- '()', then the generated λ{(): ...} inherits that original location.
match d span book x ms (([p], u) : _) | isUnitPat p =
  let mloc = unitPatLoc p in
  let body = lam d (map fst ms) $ desugarPatsCore d span book u in
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
  let if_tup = Lam (patOf d a) Nothing $ \_ -> Lam (patOf (d+1) b) Nothing $ \_ -> lam d (map fst ms) $ desugarPatsCore (d+2) span book p in
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
      in ((s, lam d (map fst ms) $ desugarPatsCore d span book rhs) : cs, def)
    collect (([(cut -> Var k _)], rhs) : _) =
      ([], Just $ Lam k Nothing $ \_ -> lam d (map fst ms) $ desugarPatsCore (d+1) span book rhs)
    collect (c:_) = errorWithSpan span "Invalid pattern: invalid Sym case"

-- match x { &L{a,b}: s }
-- ---------------------------
-- ~ x { &L{,}: λa. λb. s }
match d span book x ms (([(cut -> Sup l a b)], s) : _) =
  apps d (map snd ms) $ App (SupM l if_sup) x
  where if_sup = Lam (patOf d a) Nothing $ \_ -> Lam (patOf (d+1) b) Nothing $ \_ -> lam d (map fst ms) $ desugarPatsCore (d+2) span book s

-- match x { Rfl: r }
-- ------------------
-- ~x { Rfl: r }
match d span book x ms (([(cut -> Rfl)], r) : _) =
  apps d (map snd ms) $ App (EqlM (lam d (map fst ms) $ desugarPatsCore d span book r)) x

-- match x { k: body }
-- -------------------
-- body[k := x]
match d span book x ms (([(cut -> Var k i)], body) : _) =
  lam d (map fst ms) $ desugarPatsCore d span book (shove d ((k, x) : ms) body)

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

-- Default Specialization
-- ----------------------

specializeDefaultsCore :: Int -> Book -> Term -> Term
specializeDefaultsCore d book term = case term of
  -- Variables
  Var n i -> Var n i
  Ref n i -> Ref n i
  Sub t   -> Sub (specializeDefaultsCore d book t)
  
  -- Definitions
  Fix n f      -> Fix n (\x -> specializeDefaultsCore (d+1) book (f x))
  Let k t v f  -> Let k (fmap (specializeDefaultsCore d book) t) (specializeDefaultsCore d book v) (\x -> specializeDefaultsCore (d+1) book (f x))
  Use k v f    -> Use k (specializeDefaultsCore d book v) (\x -> specializeDefaultsCore (d+1) book (f x))
  
  -- Universe
  Set -> Set
  
  -- Annotation
  Chk x t -> Chk (specializeDefaultsCore d book x) (specializeDefaultsCore d book t)
  Tst x   -> Tst (specializeDefaultsCore d book x)
  
  -- Empty
  Emp  -> Emp
  EmpM -> EmpM
  
  -- Unit
  Uni       -> Uni
  One       -> One
  UniM f    -> UniM (specializeDefaultsCore d book f)
  
  -- Bool
  Bit       -> Bit
  Bt0       -> Bt0
  Bt1       -> Bt1
  BitM f t  -> BitM (specializeDefaultsCore d book f) (specializeDefaultsCore d book t)
  
  -- Nat
  Nat       -> Nat
  Zer       -> Zer
  Suc n     -> Suc (specializeDefaultsCore d book n)
  NatM z s  -> NatM (specializeDefaultsCore d book z) (specializeDefaultsCore d book s)
  
  -- List
  Lst t     -> Lst (specializeDefaultsCore d book t)
  Nil       -> Nil
  Con h t   -> Con (specializeDefaultsCore d book h) (specializeDefaultsCore d book t)
  LstM n c  -> LstM (specializeDefaultsCore d book n) (specializeDefaultsCore d book c)
  
  -- Enum
  Enu s     -> Enu s
  Sym s     -> Sym s
  EnuM c e  -> EnuM [(s, specializeDefaultsCore d book t) | (s, t) <- c] (fmap (specializeDefaultsCore d book) e)
  
  -- Pair
  Sig a b   -> Sig (specializeDefaultsCore d book a) (specializeDefaultsCore d book b)
  Tup a b   -> Tup (specializeDefaultsCore d book a) (specializeDefaultsCore d book b)
  
  -- Special case: SigM with pattern matching structure
  SigM lam -> case lam of
    Lam n1 t1 f1 ->
      case f1 (Var n1 0) of
        Lam n2 t2 f2 ->
          case f2 (Var n2 0) of
            App enumTerm scrutinee ->
              case cut enumTerm of
                EnuM cases def ->
                  SigM (Lam n1 t1 (\x1 -> Lam n2 t2 (\x2 -> App (specializeEnuM d book cases def n2) scrutinee)))
                _ -> SigM (Lam n1 t1 (\x -> specializeDefaultsCore (d+1) book (f1 x)))
            _ -> SigM (Lam n1 t1 (\x -> specializeDefaultsCore (d+1) book (f1 x)))
        _ -> SigM (Lam n1 t1 (\x -> specializeDefaultsCore (d+1) book (f1 x)))
    _ -> SigM (specializeDefaultsCore d book lam)
  
  -- Function
  All a b   -> All (specializeDefaultsCore d book a) (specializeDefaultsCore d book b)
  Lam n t f -> Lam n (fmap (specializeDefaultsCore d book) t) (\x -> specializeDefaultsCore (d+1) book (f x))
  App f x   -> App (specializeDefaultsCore d book f) (specializeDefaultsCore d book x)
  
  -- Equality
  Eql t a b -> Eql (specializeDefaultsCore d book t) (specializeDefaultsCore d book a) (specializeDefaultsCore d book b)
  Rfl       -> Rfl
  EqlM f    -> EqlM (specializeDefaultsCore d book f)
  Rwt e f   -> Rwt (specializeDefaultsCore d book e) (specializeDefaultsCore d book f)
  
  -- MetaVar
  Met i t x -> Met i (specializeDefaultsCore d book t) (map (specializeDefaultsCore d book) x)
  
  -- Superposition
  Era       -> Era
  Sup l a b -> Sup (specializeDefaultsCore d book l) (specializeDefaultsCore d book a) (specializeDefaultsCore d book b)
  SupM l f  -> SupM (specializeDefaultsCore d book l) (specializeDefaultsCore d book f)
  
  -- Errors
  Loc s t   -> Loc s (specializeDefaultsCore d book t)
  
  -- Logging
  Log s x   -> Log (specializeDefaultsCore d book s) (specializeDefaultsCore d book x)
  
  -- Primitive
  Pri p     -> Pri p
  
  -- Numbers
  Num t     -> Num t
  Val v     -> Val v
  Op2 o a b -> Op2 o (specializeDefaultsCore d book a) (specializeDefaultsCore d book b)
  Op1 o a   -> Op1 o (specializeDefaultsCore d book a)
  
  -- Sugars (should not appear after desugaring)
  Pat _ _ _ -> error "Pattern should not appear after desugaring"
  Frk l a b -> Frk (specializeDefaultsCore d book l) (specializeDefaultsCore d book a) (specializeDefaultsCore d book b)

-- Internal helpers for specialization
-- ------------------------------------

-- Find which type a set of constructors belongs to
findTypeForConstructors :: Book -> [String] -> Maybe (Name, [(String, Int)])
findTypeForConstructors (Book _ _ typeCtors) ctors =
  case filter matchesType (M.toList typeCtors) of
    ((typeName, ctorList):_) -> Just (typeName, ctorList)
    []                        -> Nothing
  where
    matchesType (_, typeCtrList) = any (`elem` map fst typeCtrList) ctors

-- Specialize a single constructor by adding it to the match with the default body
-- The structure of a constructor is sigma pairs ending with unit. Fields are
-- bound sequentially and the constructor symbol is bound with a use statement.
specializeConstructor :: String -> Int -> Term -> String -> Term
specializeConstructor ctorName arity (Lam k _ defaultBody) scrutineeName =
  let body = defaultBody (Var k 0) in
  buildSigmaChain arity body scrutineeName ctorName k
specializeConstructor _ _ term _ = term

-- Build sigma chain for constructor with given arity
buildSigmaChain :: Int -> Term -> String -> String -> String -> Term
buildSigmaChain arity body scrutineeName ctorName defaultVar =
  buildSigmaChainRec arity body scrutineeName ctorName defaultVar []

-- Recursive helper for building sigma chains
buildSigmaChainRec :: Int -> Term -> String -> String -> String -> [String] -> Term
buildSigmaChainRec 0 body scrutineeName ctorName defaultVar _ =
  -- Base case: bind constructor symbol and apply to unit match
  let bodyWithUse = Use defaultVar (Sym ctorName) (\_ -> body) in
  App (UniM bodyWithUse) (Var scrutineeName 0)
buildSigmaChainRec arity body originalScrutinee ctorName defaultVar fieldVars =
  -- Recursive case: build nested sigma matches for fields
  let fieldVar = "$field" ++ show arity
      contVar  = "$cont" ++ show arity
      newFieldVars = fieldVar : fieldVars
      innerChain = buildSigmaChainRec (arity - 1) body contVar ctorName defaultVar newFieldVars in
  App (SigM (Lam fieldVar Nothing (\_ -> Lam contVar Nothing (\_ -> innerChain)))) (Var originalScrutinee 0)

-- Specializes an EnuM term by replacing default cases with explicit constructor cases
specializeEnuM :: Int -> Book -> [(String, Term)] -> Maybe Term -> String -> Term
specializeEnuM d book cases Nothing scrutineeName =
  -- No default case: just recurse on existing cases
  EnuM [(s, specializeDefaultsCore d book t) | (s, t) <- cases] Nothing
specializeEnuM d book cases (Just defaultTerm) scrutineeName =
  -- Has default case: expand to all missing constructors
  EnuM (existingCases ++ newCases) Nothing
  where
    presentCases  = map fst cases
    typeInfo      = findTypeForConstructors book presentCases
    missingCtors  = case typeInfo of
      Just (_, allCtors) -> filter (\(name, _) -> name `notElem` presentCases) allCtors
      Nothing            -> []
    existingCases = [(s, specializeDefaultsCore d book t) | (s, t) <- cases]
    newCases      = [(name, specializeConstructor name arity defaultTerm scrutineeName) | (name, arity) <- missingCtors]