{-# LANGUAGE ViewPatterns #-}

-- Pattern Desugaring
-- ==================
-- Converts all Pats to native expression-based matches.

module Core.Adjust.DesugarPats where

import Core.Bind
import Core.Show
import Core.Type
import Core.WHNF
import qualified Data.Set as S
import Debug.Trace (trace)

desugarPats :: Int -> Span -> Term -> Term
desugarPats d span (Var n i)       = Var n i
desugarPats d span (Ref n i)       = Ref n i
desugarPats d span (Sub t)         = Sub (desugarPats d span t)
desugarPats d span (Fix n f)       = Fix n (\x -> desugarPats (d+1) span (f x))
desugarPats d span (Let k t v f)   = Let k (fmap (desugarPats d span) t) (desugarPats d span v) (\x -> desugarPats (d+1) span (f x))
desugarPats d span (Use k v f)     = Use k (desugarPats d span v) (\x -> desugarPats (d+1) span (f x))
desugarPats d span Set             = Set
desugarPats d span (Chk x t)       = Chk (desugarPats d span x) (desugarPats d span t)
desugarPats d span (Tst x)         = Tst (desugarPats d span x)
desugarPats d span Emp             = Emp
desugarPats d span EmpM            = EmpM
desugarPats d span Uni             = Uni
desugarPats d span One             = One
desugarPats d span (UniM f)        = UniM (desugarPats d span f)
desugarPats d span Bit             = Bit
desugarPats d span Bt0             = Bt0
desugarPats d span Bt1             = Bt1
desugarPats d span (BitM f t)      = BitM (desugarPats d span f) (desugarPats d span t)
desugarPats d span Nat             = Nat
desugarPats d span Zer             = Zer
desugarPats d span (Suc n)         = Suc (desugarPats d span n)
desugarPats d span (NatM z s)      = NatM (desugarPats d span z) (desugarPats d span s)
desugarPats d span (Lst t)         = Lst (desugarPats d span t)
desugarPats d span Nil             = Nil
desugarPats d span (Con h t)       = Con (desugarPats d span h) (desugarPats d span t)
desugarPats d span (LstM n c)      = LstM (desugarPats d span n) (desugarPats d span c)
desugarPats d span (Enu s)         = Enu s
desugarPats d span (Sym s)         = Sym s
desugarPats d span (EnuM c e)      = EnuM [(s, desugarPats d span t) | (s, t) <- c] (desugarPats d span e)
desugarPats d span (Sig a b)       = Sig (desugarPats d span a) (desugarPats d span b)
desugarPats d span (Tup a b)       = Tup (desugarPats d span a) (desugarPats d span b)
desugarPats d span (SigM f)        = SigM (desugarPats d span f)
desugarPats d span (All a b)       = All (desugarPats d span a) (desugarPats d span b)
desugarPats d span (Lam n t f)     = Lam n (fmap (desugarPats d span) t) (\x -> desugarPats (d+1) span (f x))
desugarPats d span (App f x)       = App (desugarPats d span f) (desugarPats d span x)
desugarPats d span (Eql t a b)     = Eql (desugarPats d span t) (desugarPats d span a) (desugarPats d span b)
desugarPats d span Rfl             = Rfl
desugarPats d span (EqlM f)        = EqlM (desugarPats d span f)
desugarPats d span (Met i t x)     = Met i (desugarPats d span t) (map (desugarPats d span) x)
desugarPats d span Era             = Era
desugarPats d span (Sup l a b)     = Sup (desugarPats d span l) (desugarPats d span a) (desugarPats d span b)
desugarPats d span (SupM l f)      = SupM (desugarPats d span l) (desugarPats d span f)
desugarPats d span (Frk l a b)     = Frk (desugarPats d span l) (desugarPats d span a) (desugarPats d span b)
desugarPats d span (Rwt e f)       = Rwt (desugarPats d span e) (desugarPats d span f)
desugarPats d span (Num t)         = Num t
desugarPats d span (Val v)         = Val v
desugarPats d span (Op2 o a b)     = Op2 o (desugarPats d span a) (desugarPats d span b)
desugarPats d span (Op1 o a)       = Op1 o (desugarPats d span a)
desugarPats d span (Pri p)         = Pri p
desugarPats d span (Log s x)       = Log (desugarPats d span s) (desugarPats d span x)
desugarPats d span (Loc s t)       = Loc s (desugarPats d s t)
desugarPats d span (Pat [s] ms cs) = match d span s ms cs
desugarPats d span (Pat ss  ms []) = One
desugarPats d span (Pat ss  ms cs) = errorWithSpan span "Invalid pattern: multiple scrutinees after flattening"

match :: Int -> Span -> Term -> [Move] -> [Case] -> Term

-- match x { 0n: z ; 1n+p: s }
-- ---------------------------
-- ~x { 0n: z ; 1n+: λp. s }
match d span x ms (([(cut -> Zer)], z) : ([(cut -> Suc p)], s) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ desugarPats d span z
        if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) $ desugarPats (d+1) span s

-- match x { 1n+p: s ; 0n: z }
-- ---------------------------
-- ~x { 0n: z ; 1n+: λp. s }
match d span x ms (([(cut -> Suc p)], s) : ([(cut -> Zer)], z) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ desugarPats d span z
        if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) $ desugarPats (d+1) span s

-- match x { 0n: z ; k: v }
-- --------------------------------------
-- ~x { 0n: z ; 1n+: λk. v[k := 1n+k] }
match d span x ms (([(cut -> Zer)], z) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ desugarPats d span z
        if_suc = Lam k (Just Nat) $ \x -> lam d (map fst ms) $ desugarPats (d+1) span (bindVarByName k (Suc (Var k 0)) v)

-- match x { 1n+p: s ; k: v }
-- ------------------------------------
-- ~x { 0n: v[k := 0n] ; 1n+: λp. s }
match d span x ms (([(cut -> Suc p)], s) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (NatM if_zer if_suc) x
  where if_zer = lam d (map fst ms) $ desugarPats d span (bindVarByName k Zer v)
        if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) $ desugarPats (d+1) span s

-- match x { False: f ; True: t }
-- ------------------------------
-- ~x { False: f ; True: t }
match d span x ms (([(cut -> Bt0)], f) : ([(cut -> Bt1)], t) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ desugarPats d span f) (lam d (map fst ms) $ desugarPats d span t)) x

-- match x { True: t ; False: f }
-- ------------------------------
-- ~x { False: f ; True: t }
match d span x ms (([(cut -> Bt1)], t) : ([(cut -> Bt0)], f) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ desugarPats d span f) (lam d (map fst ms) $ desugarPats d span t)) x

-- match x { False: f ; k: v }
-- --------------------------------------
-- ~x { False: f ; True: v[k := True] }
match d span x ms (([(cut -> Bt0)], f) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ desugarPats d span f) (lam d (map fst ms) $ desugarPats d span (bindVarByName k Bt1 v))) x

-- match x { True: t ; k: v }
-- ---------------------------------------
-- ~x { False: v[k := False] ; True: t }
match d span x ms (([(cut -> Bt1)], t) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (BitM (lam d (map fst ms) $ desugarPats d span (bindVarByName k Bt0 v)) (lam d (map fst ms) $ desugarPats d span t)) x

-- match x { []: n ; h<>t: c }
-- ------------------------------
-- ~x { []: n ; <>: λh. λt. c }
match d span x ms (([(cut -> Nil)], n) : ([(cut -> Con h t)], c) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ desugarPats d span n
        if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+2) span c

-- match x { h<>t: c ; []: n }
-- ------------------------------
-- ~x { []: n ; <>: λh. λt. c }
match d span x ms (([(cut -> Con h t)], c) : ([(cut -> Nil)], n) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ desugarPats d span n
        if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+2) span c

-- match x { []: n ; k: v }
-- -----------------------------------------
-- ~x { []: n ; <>: λh. λt. v[k := h<>t] }
match d span x ms (([(cut -> Nil)], n) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ desugarPats d span n
        if_con = Lam (nam d) Nothing $ \_ -> Lam (nam (d+1)) Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+2) span (bindVarByName k (Con (var d) (var (d+1))) v)

-- match x { h<>t: c ; k: v }
-- ---------------------------------------
-- ~x { []: v[k := []] ; <>: λh. λt. c }
match d span x ms (([(cut -> Con h t)], c) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ App (LstM if_nil if_con) x
  where if_nil = lam d (map fst ms) $ desugarPats d span (bindVarByName k Nil v)
        if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+2) span c

-- match x { (): u }
-- -----------------
-- ~x { (): u }
-- Preserve location from the unit pattern: if the case pattern is a located
-- '()', then the generated λ{(): ...} inherits that original location.
match d span x ms (([p], u) : _) | isUnitPat p =
  let mloc = unitPatLoc p in
  let body = lam d (map fst ms) $ desugarPats d span u in
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
match d span x ms (([tup], p) : _) | isTupPat tup =
  let mloc = tupPatLoc tup in
  let (a, b) = tupPatFields tup in
  let if_tup = Lam (patOf d a) Nothing $ \_ -> Lam (patOf (d+1) b) Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+2) span p in
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
-- ~x { @S1:b1 ; @S2:b2 ; ... ; d }
match d span x ms cs@(([(cut -> Sym _)], _) : _) =
  let (cBranches, defBranch) = collect cs
      enumMatch = case span of
        Span (0,0) (0,0) _ _ -> EnuM cBranches defBranch  -- noSpan case
        _                    -> Loc span (EnuM cBranches defBranch)
  in apps d (map snd ms) $ App enumMatch x
  where
    collect :: [Case] -> ([(String, Term)], Term)
    collect [] = ([], Lam "_" Nothing $ \_ -> lam d (map fst ms) $ One)
    collect (([(cut -> Sym s)], rhs) : rest) =
      let (cs, def) = collect rest
      in ((s, lam d (map fst ms) $ desugarPats d span rhs) : cs, def)
    collect (([(cut -> Var k _)], rhs) : _) =
      ([], Lam k Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+1) span rhs)
    collect (c:_) = errorWithSpan span "Invalid pattern: invalid Sym case"

-- match x { &L{a,b}: s }
-- ---------------------------
-- ~ x { &L{,}: λa. λb. s }
match d span x ms (([(cut -> Sup l a b)], s) : _) =
  apps d (map snd ms) $ App (SupM l if_sup) x
  where if_sup = Lam (patOf d a) Nothing $ \_ -> Lam (patOf (d+1) b) Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+2) span s

-- match x { Rfl: r }
-- ------------------
-- ~x { Rfl: r }
match d span x ms (([(cut -> Rfl)], r) : _) =
  apps d (map snd ms) $ App (EqlM (lam d (map fst ms) $ desugarPats d span r)) x

-- match x { k: body }
-- -------------------
-- body[k := x]
match d span x ms (([(cut -> Var k i)], body) : _) =
  lam d (map fst ms) $ desugarPats d span (shove d ((k, x) : ms) body)

-- match x { }
-- -----------
-- λ{}
match d span x ms [] =
  let empMatch = case span of
        Span (0,0) (0,0) _ _ -> EmpM  -- Keep noSpan as raw EmpM
        _                    -> Loc span EmpM  -- Preserve location for error reporting
  in apps d (map snd ms) (App empMatch x)

-- Invalid pattern
-- match d span s ms cs = error $ "match - invalid pattern: " ++ show (d, s, ms, cs) ++ "\n" ++ show span
match d span s ms cs = errorWithSpan span "Invalid pattern."

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
