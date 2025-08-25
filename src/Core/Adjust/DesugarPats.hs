{-# LANGUAGE ViewPatterns #-}

-- Pattern Desugaring
-- ==================
-- Converts all Pats to native expression-based matches.

module Core.Adjust.DesugarPats where

import Core.Bind
import Core.Show
import Core.Type
import Core.WHNF
import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace (trace)

desugarPats :: Int -> Span -> Book -> Term -> Term
desugarPats d span book (Var n i)       = Var n i
desugarPats d span book (Ref n i)       = Ref n i
desugarPats d span book (Sub t)         = Sub (desugarPats d span book t)
desugarPats d span book (Fix n f)       = Fix n (\x -> desugarPats (d+1) span book (f x))
desugarPats d span book (Let k t v f)   = Let k (fmap (desugarPats d span book) t) (desugarPats d span book v) (\x -> desugarPats (d+1) span book (f x))
desugarPats d span book (Use k v f)     = Use k (desugarPats d span book v) (\x -> desugarPats (d+1) span book (f x))
desugarPats d span book Set             = Set
desugarPats d span book (Chk x t)       = Chk (desugarPats d span book x) (desugarPats d span book t)
desugarPats d span book (Tst x)         = Tst (desugarPats d span book x)
desugarPats d span book Emp             = Emp
desugarPats d span book EmpM            = EmpM
desugarPats d span book Uni             = Uni
desugarPats d span book One             = One
desugarPats d span book (UniM f)        = UniM (desugarPats d span book f)
desugarPats d span book Bit             = Bit
desugarPats d span book Bt0             = Bt0
desugarPats d span book Bt1             = Bt1
desugarPats d span book (BitM f t)      = BitM (desugarPats d span book f) (desugarPats d span book t)
desugarPats d span book Nat             = Nat
desugarPats d span book Zer             = Zer
desugarPats d span book (Suc n)         = Suc (desugarPats d span book n)
desugarPats d span book (NatM z s)      = NatM (desugarPats d span book z) (desugarPats d span book s)
desugarPats d span book (Lst t)         = Lst (desugarPats d span book t)
desugarPats d span book Nil             = Nil
desugarPats d span book (Con h t)       = Con (desugarPats d span book h) (desugarPats d span book t)
desugarPats d span book (LstM n c)      = LstM (desugarPats d span book n) (desugarPats d span book c)
desugarPats d span book (Enu s)         = Enu s
desugarPats d span book (Sym s)         = Sym s
desugarPats d span book (EnuM c e)      = EnuM [(s, desugarPats d span book t) | (s, t) <- c] (fmap (desugarPats d span book) e)
desugarPats d span book (Sig a b)       = Sig (desugarPats d span book a) (desugarPats d span book b)
desugarPats d span book (Tup a b)       = Tup (desugarPats d span book a) (desugarPats d span book b)
desugarPats d span book (SigM f)        = SigM (desugarPats d span book f)
desugarPats d span book (All a b)       = All (desugarPats d span book a) (desugarPats d span book b)
desugarPats d span book (Lam n t f)     = Lam n (fmap (desugarPats d span book) t) (\x -> desugarPats (d+1) span book (f x))
desugarPats d span book (App f x)       = App (desugarPats d span book f) (desugarPats d span book x)
desugarPats d span book (Eql t a b)     = Eql (desugarPats d span book t) (desugarPats d span book a) (desugarPats d span book b)
desugarPats d span book Rfl             = Rfl
desugarPats d span book (EqlM f)        = EqlM (desugarPats d span book f)
desugarPats d span book (Met i t x)     = Met i (desugarPats d span book t) (map (desugarPats d span book) x)
desugarPats d span book Era             = Era
desugarPats d span book (Sup l a b)     = Sup (desugarPats d span book l) (desugarPats d span book a) (desugarPats d span book b)
desugarPats d span book (SupM l f)      = SupM (desugarPats d span book l) (desugarPats d span book f)
desugarPats d span book (Frk l a b)     = Frk (desugarPats d span book l) (desugarPats d span book a) (desugarPats d span book b)
desugarPats d span book (Rwt e f)       = Rwt (desugarPats d span book e) (desugarPats d span book f)
desugarPats d span book (Num t)         = Num t
desugarPats d span book (Val v)         = Val v
desugarPats d span book (Op2 o a b)     = Op2 o (desugarPats d span book a) (desugarPats d span book b)
desugarPats d span book (Op1 o a)       = Op1 o (desugarPats d span book a)
desugarPats d span book (Pri p)         = Pri p
desugarPats d span book (Log s x)       = Log (desugarPats d span book s) (desugarPats d span book x)
desugarPats d span book (Loc s t)       = Loc s (desugarPats d s book t)
desugarPats d span book (Pat [s] ms cs) = match d span book s ms cs
desugarPats d span book (Pat ss  ms []) = One
desugarPats d span book (Pat ss  ms cs) = errorWithSpan span "Invalid pattern: multiple scrutinees after flattening"

match :: Int -> Span -> Book -> Term -> [Move] -> [Case] -> Term

-- match x { 0n: z ; 1n+p: s }
-- ---------------------------
-- ~x { 0n: z ; 1n+: λp. s }
match d span book x ms (([(cut -> Zer)], z) : ([(cut -> Suc p)], s) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ desugarPats d span book z
        if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) $ desugarPats (d+1) span book s

-- match x { 1n+p: s ; 0n: z }
-- ---------------------------
-- ~x { 0n: z ; 1n+: λp. s }
match d span book x ms (([(cut -> Suc p)], s) : ([(cut -> Zer)], z) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ desugarPats d span book z
        if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) $ desugarPats (d+1) span book s

-- match x { 0n: z ; k: v }
-- --------------------------------------
-- ~x { 0n: z ; 1n+: λk. v[k := 1n+k] }
match d span book x ms (([(cut -> Zer)], z) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ desugarPats d span book z
        if_suc = Lam k (Just Nat) $ \x -> lam d (map fst ms) $ desugarPats (d+1) span book (bindVarByName k (Suc (Var k 0)) v)

-- match x { 1n+p: s ; k: v }
-- ------------------------------------
-- ~x { 0n: v[k := 0n] ; 1n+: λp. s }
match d span book x ms (([(cut -> Suc p)], s) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ desugarPats d span book (bindVarByName k Zer v)
        if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) $ desugarPats (d+1) span book s

-- match x { False: f ; True: t }
-- ------------------------------
-- ~x { False: f ; True: t }
match d span book x ms (([(cut -> Bt0)], f) : ([(cut -> Bt1)], t) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ desugarPats d span book f) (lam d (map fst ms) $ desugarPats d span book t)) x

-- match x { True: t ; False: f }
-- ------------------------------
-- ~x { False: f ; True: t }
match d span book x ms (([(cut -> Bt1)], t) : ([(cut -> Bt0)], f) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ desugarPats d span book f) (lam d (map fst ms) $ desugarPats d span book t)) x

-- match x { False: f ; k: v }
-- --------------------------------------
-- ~x { False: f ; True: v[k := True] }
match d span book x ms (([(cut -> Bt0)], f) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ desugarPats d span book f) (lam d (map fst ms) $ desugarPats d span book (bindVarByName k Bt1 v))) x

-- match x { True: t ; k: v }
-- ---------------------------------------
-- ~x { False: v[k := False] ; True: t }
match d span book x ms (([(cut -> Bt1)], t) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ desugarPats d span book (bindVarByName k Bt0 v)) (lam d (map fst ms) $ desugarPats d span book t)) x

-- match x { []: n ; h<>t: c }
-- ------------------------------
-- ~x { []: n ; <>: λh. λt. c }
match d span book x ms (([(cut -> Nil)], n) : ([(cut -> Con h t)], c) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ desugarPats d span book n
        if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+2) span book c

-- match x { h<>t: c ; []: n }
-- ------------------------------
-- ~x { []: n ; <>: λh. λt. c }
match d span book x ms (([(cut -> Con h t)], c) : ([(cut -> Nil)], n) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ desugarPats d span book n
        if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+2) span book c

-- match x { []: n ; k: v }
-- -----------------------------------------
-- ~x { []: n ; <>: λh. λt. v[k := h<>t] }
match d span book x ms (([(cut -> Nil)], n) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ desugarPats d span book n
        if_con = Lam (nam d) Nothing $ \_ -> Lam (nam (d+1)) Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+2) span book (bindVarByName k (Con (var d) (var (d+1))) v)

-- match x { h<>t: c ; k: v }
-- ---------------------------------------
-- ~x { []: v[k := []] ; <>: λh. λt. c }
match d span book x ms (([(cut -> Con h t)], c) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ desugarPats d span book (bindVarByName k Nil v)
        if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+2) span book c

-- match x { (): u }
-- -----------------
-- ~x { (): u }
-- Preserve location from the unit pattern: if the case pattern is a located
-- '()', then the generated λ{(): ...} inherits that original location.
match d span book x ms (([p], u) : _) | isUnitPat p =
  let mloc = unitPatLoc p in
  let body = lam d (map fst ms) $ desugarPats d span book u in
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
  let if_tup = Lam (patOf d a) Nothing $ \_ -> Lam (patOf (d+1) b) Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+2) span book p in
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
-- ~x { @S1:b1 ; @S2:b2 ; ... ; @Sn:d[k := @Sn] ; ... }
match d span book x ms cs@(([(cut -> Sym _)], _) : _) =
  let (cBranches, defBranch, defVar) = collect cs
      -- Try to find the type name from the constructor names
      allConstructors = case cBranches of
        [] -> []
        ((ctr,_):_) -> findTypeConstructors book ctr
      -- Specialize default branch for missing constructors
      missingCtrs = filter (\c -> not (any ((== c) . fst) cBranches)) allConstructors
      specializedBranches = cBranches ++ 
        (case defVar of
          Nothing -> []
          Just (k, defBody) -> map (\ctr -> (ctr, specializeDef d k ctr defBody)) missingCtrs)
      -- Create the final default branch (should not be reached if all constructors are covered)
      -- If we have all constructors covered, use Nothing for default
      allCovered = not (null allConstructors) && 
                   length specializedBranches == length allConstructors
      finalDefault = if allCovered
        then Nothing  -- No default needed when all constructors are covered
        else case defVar of
          Nothing -> Just $ Lam "_" Nothing $ \_ -> lam d (map fst ms) $ One
          Just (k, defBody) -> Just $ Lam k Nothing $ \_ -> lam d (map fst ms) $ defBody
      enumMatch = case span of
        Span (0,0) (0,0) _ _ -> EnuM specializedBranches finalDefault
        _                    -> Loc span (EnuM specializedBranches finalDefault)
  in apps d (map snd ms) $ App enumMatch x
  where
    collect :: [Case] -> ([(String, Term)], Maybe Term, Maybe (String, Term))
    collect [] = ([], Nothing, Nothing)
    collect (([(cut -> Sym s)], rhs) : rest) =
      let (cs, def, defVar) = collect rest
      in ((s, lam d (map fst ms) $ desugarPats d span book rhs) : cs, def, defVar)
    collect (([(cut -> Var k _)], rhs) : _) =
      ([], Just $ Lam k Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+1) span book rhs, 
       Just (k, desugarPats (d+1) span book rhs))
    collect (c:_) = errorWithSpan span "Invalid pattern: invalid Sym case"
    
    -- Specialize default case for a specific constructor
    specializeDef :: Int -> String -> String -> Term -> Term
    specializeDef depth varName ctrName body =
      lam depth (map fst ms) $ Use varName (Sym ctrName) $ \_ -> body
    
    -- Find all constructors for a type given one constructor name
    findTypeConstructors :: Book -> String -> [String]
    findTypeConstructors (Book _ _ typeCtrs) ctrName =
      case findTypeForConstructor typeCtrs ctrName of
        Nothing -> []
        Just typeName -> case M.lookup typeName typeCtrs of
          Nothing -> []
          Just ctrs -> ctrs
    
    -- Find which type a constructor belongs to
    findTypeForConstructor :: M.Map Name [String] -> String -> Maybe Name
    findTypeForConstructor typeCtrs ctrName =
      case [(tName, ctrs) | (tName, ctrs) <- M.toList typeCtrs, ctrName `elem` ctrs] of
        [] -> Nothing
        ((tName, _):_) -> Just tName

-- match x { &L{a,b}: s }
-- ---------------------------
-- ~ x { &L{,}: λa. λb. s }
match d span book x ms (([(cut -> Sup l a b)], s) : _) =
  apps d (map snd ms) $ App (SupM l if_sup) x
  where if_sup = Lam (patOf d a) Nothing $ \_ -> Lam (patOf (d+1) b) Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+2) span book s

-- match x { Rfl: r }
-- ------------------
-- ~x { Rfl: r }
match d span book x ms (([(cut -> Rfl)], r) : _) =
  apps d (map snd ms) $ App (EqlM (lam d (map fst ms) $ desugarPats d span book r)) x

-- match x { k: body }
-- -------------------
-- body[k := x]
match d span book x ms (([(cut -> Var k i)], body) : _) =
  lam d (map fst ms) $ desugarPats d span book (shove d ((k, x) : ms) body)

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
