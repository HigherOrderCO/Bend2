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

desugarPats :: Int -> Span -> Term -> Result Term
desugarPats d span (Var n i)       = Done $ Var n i
desugarPats d span (Ref n i)       = Done $ Ref n i
desugarPats d span (Sub t)         = do
  t' <- desugarPats d span t
  Done $ Sub t'
desugarPats d span (Fix n f)       = Done $ Fix n (\x -> case desugarPats (d+1) span (f x) of Done t -> t; Fail e -> error $ show e)
desugarPats d span (Let k t v f)   = do
  t' <- mapM (desugarPats d span) t
  v' <- desugarPats d span v
  Done $ Let k t' v' (\x -> case desugarPats (d+1) span (f x) of Done t -> t; Fail e -> error $ show e)
desugarPats d span (Use k v f)     = do
  v' <- desugarPats d span v
  Done $ Use k v' (\x -> case desugarPats (d+1) span (f x) of Done t -> t; Fail e -> error $ show e)
desugarPats d span Set             = Done Set
desugarPats d span (Chk x t)       = do
  x' <- desugarPats d span x
  t' <- desugarPats d span t
  Done $ Chk x' t'
desugarPats d span (Tst x)         = do
  x' <- desugarPats d span x
  Done $ Tst x'
desugarPats d span Emp             = Done Emp
desugarPats d span EmpM            = Done EmpM
desugarPats d span Uni             = Done Uni
desugarPats d span One             = Done One
desugarPats d span (UniM f)        = do
  f' <- desugarPats d span f
  Done $ UniM f'
desugarPats d span Bit             = Done Bit
desugarPats d span Bt0             = Done Bt0
desugarPats d span Bt1             = Done Bt1
desugarPats d span (BitM f t)      = do
  f' <- desugarPats d span f
  t' <- desugarPats d span t
  Done $ BitM f' t'
desugarPats d span Nat             = Done Nat
desugarPats d span Zer             = Done Zer
desugarPats d span (Suc n)         = do
  n' <- desugarPats d span n
  Done $ Suc n'
desugarPats d span (NatM z s)      = do
  z' <- desugarPats d span z
  s' <- desugarPats d span s
  Done $ NatM z' s'
desugarPats d span (Lst t)         = do
  t' <- desugarPats d span t
  Done $ Lst t'
desugarPats d span Nil             = Done Nil
desugarPats d span (Con h t)       = do
  h' <- desugarPats d span h
  t' <- desugarPats d span t
  Done $ Con h' t'
desugarPats d span (LstM n c)      = do
  n' <- desugarPats d span n
  c' <- desugarPats d span c
  Done $ LstM n' c'
desugarPats d span (Enu s)         = Done $ Enu s
desugarPats d span (Sym s)         = Done $ Sym s
desugarPats d span (EnuM c e)      = do
  c' <- mapM (\(s, t) -> do t' <- desugarPats d span t; Done (s, t')) c
  e' <- desugarPats d span e
  Done $ EnuM c' e'
desugarPats d span (Sig a b)       = do
  a' <- desugarPats d span a
  b' <- desugarPats d span b
  Done $ Sig a' b'
desugarPats d span (Tup a b)       = do
  a' <- desugarPats d span a
  b' <- desugarPats d span b
  Done $ Tup a' b'
desugarPats d span (SigM f)        = do
  f' <- desugarPats d span f
  Done $ SigM f'
desugarPats d span (All a b)       = do
  a' <- desugarPats d span a
  b' <- desugarPats d span b
  Done $ All a' b'
desugarPats d span (Lam n t f)     = do
  t' <- mapM (desugarPats d span) t
  Done $ Lam n t' (\x -> case desugarPats (d+1) span (f x) of Done t -> t; Fail e -> error $ show e)
desugarPats d span (App f x)       = do
  f' <- desugarPats d span f
  x' <- desugarPats d span x
  Done $ App f' x'
desugarPats d span (Eql t a b)     = do
  t' <- desugarPats d span t
  a' <- desugarPats d span a
  b' <- desugarPats d span b
  Done $ Eql t' a' b'
desugarPats d span Rfl             = Done Rfl
desugarPats d span (EqlM f)        = do
  f' <- desugarPats d span f
  Done $ EqlM f'
desugarPats d span (Met i t x)     = do
  t' <- desugarPats d span t
  x' <- mapM (desugarPats d span) x
  Done $ Met i t' x'
desugarPats d span Era             = Done Era
desugarPats d span (Sup l a b)     = do
  l' <- desugarPats d span l
  a' <- desugarPats d span a
  b' <- desugarPats d span b
  Done $ Sup l' a' b'
desugarPats d span (SupM l f)      = do
  l' <- desugarPats d span l
  f' <- desugarPats d span f
  Done $ SupM l' f'
desugarPats d span (Frk l a b)     = do
  l' <- desugarPats d span l
  a' <- desugarPats d span a
  b' <- desugarPats d span b
  Done $ Frk l' a' b'
desugarPats d span (Rwt e f)       = do
  e' <- desugarPats d span e
  f' <- desugarPats d span f
  Done $ Rwt e' f'
desugarPats d span (Num t)         = Done $ Num t
desugarPats d span (Val v)         = Done $ Val v
desugarPats d span (Op2 o a b)     = do
  a' <- desugarPats d span a
  b' <- desugarPats d span b
  Done $ Op2 o a' b'
desugarPats d span (Op1 o a)       = do
  a' <- desugarPats d span a
  Done $ Op1 o a'
desugarPats d span (Pri p)         = Done $ Pri p
desugarPats d span (Log s x)       = do
  s' <- desugarPats d span s
  x' <- desugarPats d span x
  Done $ Log s' x'
desugarPats d span (Loc s t)       = do
  t' <- desugarPats d s t
  Done $ Loc s t'
desugarPats d span (Pat [s] ms cs) = match d span s ms cs
desugarPats d span (Pat ss  ms []) = Done One
desugarPats d span (Pat ss  ms cs) = Fail $ Unsupported span (Ctx []) (Just "Invalid pattern: multiple scrutinees after flattening")

match :: Int -> Span -> Term -> [Move] -> [Case] -> Result Term

-- match x { 0n: z ; 1n+p: s }
-- ---------------------------
-- ~x { 0n: z ; 1n+: λp. s }
match d span x ms (([(cut -> Zer)], z) : ([(cut -> Suc p)], s) : _) = do
  z' <- desugarPats d span z
  s' <- desugarPats (d+1) span s
  let if_zer = lam d (map fst ms) z'
  let if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) s'
  Done $ apps d (map snd ms) $ App (NatM if_zer if_suc) x

-- match x { 1n+p: s ; 0n: z }
-- ---------------------------
-- ~x { 0n: z ; 1n+: λp. s }
match d span x ms (([(cut -> Suc p)], s) : ([(cut -> Zer)], z) : _) = do
  z' <- desugarPats d span z
  s' <- desugarPats (d+1) span s
  let if_zer = lam d (map fst ms) z'
  let if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) s'
  Done $ apps d (map snd ms) $ App (NatM if_zer if_suc) x

-- match x { 0n: z ; k: v }
-- --------------------------------------
-- ~x { 0n: z ; 1n+: λk. v[k := 1n+k] }
match d span x ms (([(cut -> Zer)], z) : ([(cut -> Var k i)], v) : _) = do
  z' <- desugarPats d span z
  v' <- desugarPats (d+1) span (bindVarByName k (Suc (Var k 0)) v)
  let if_zer = lam d (map fst ms) z'
  let if_suc = Lam k (Just Nat) $ \x -> lam d (map fst ms) v'
  Done $ apps d (map snd ms) $ App (NatM if_zer if_suc) x

-- match x { 1n+p: s ; k: v }
-- ------------------------------------
-- ~x { 0n: v[k := 0n] ; 1n+: λp. s }
match d span x ms (([(cut -> Suc p)], s) : ([(cut -> Var k i)], v) : _) = do
  v' <- desugarPats d span (bindVarByName k Zer v)
  s' <- desugarPats (d+1) span s
  let if_zer = lam d (map fst ms) v'
  let if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) s'
  Done $ apps d (map snd ms) $ App (NatM if_zer if_suc) x

-- match x { False: f ; True: t }
-- ------------------------------
-- ~x { False: f ; True: t }
match d span x ms (([(cut -> Bt0)], f) : ([(cut -> Bt1)], t) : _) = do
  f' <- desugarPats d span f
  t' <- desugarPats d span t
  Done $ apps d (map snd ms) $ App (BitM (lam d (map fst ms) f') (lam d (map fst ms) t')) x

-- match x { True: t ; False: f }
-- ------------------------------
-- ~x { False: f ; True: t }
match d span x ms (([(cut -> Bt1)], t) : ([(cut -> Bt0)], f) : _) = do
  f' <- desugarPats d span f
  t' <- desugarPats d span t
  Done $ apps d (map snd ms) $ App (BitM (lam d (map fst ms) f') (lam d (map fst ms) t')) x

-- match x { False: f ; k: v }
-- --------------------------------------
-- ~x { False: f ; True: v[k := True] }
match d span x ms (([(cut -> Bt0)], f) : ([(cut -> Var k i)], v) : _) = do
  f' <- desugarPats d span f
  v' <- desugarPats d span (bindVarByName k Bt1 v)
  Done $ apps d (map snd ms) $ App (BitM (lam d (map fst ms) f') (lam d (map fst ms) v')) x

-- match x { True: t ; k: v }
-- ---------------------------------------
-- ~x { False: v[k := False] ; True: t }
match d span x ms (([(cut -> Bt1)], t) : ([(cut -> Var k i)], v) : _) = do
  v' <- desugarPats d span (bindVarByName k Bt0 v)
  t' <- desugarPats d span t
  Done $ apps d (map snd ms) $ App (BitM (lam d (map fst ms) v') (lam d (map fst ms) t')) x

-- match x { []: n ; h<>t: c }
-- ------------------------------
-- ~x { []: n ; <>: λh. λt. c }
match d span x ms (([(cut -> Nil)], n) : ([(cut -> Con h t)], c) : _) = do
  n' <- desugarPats d span n
  c' <- desugarPats (d+2) span c
  let if_nil = lam d (map fst ms) n'
  let if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) c'
  Done $ apps d (map snd ms) $ App (LstM if_nil if_con) x

-- match x { h<>t: c ; []: n }
-- ------------------------------
-- ~x { []: n ; <>: λh. λt. c }
match d span x ms (([(cut -> Con h t)], c) : ([(cut -> Nil)], n) : _) = do
  n' <- desugarPats d span n
  c' <- desugarPats (d+2) span c
  let if_nil = lam d (map fst ms) n'
  let if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) c'
  Done $ apps d (map snd ms) $ App (LstM if_nil if_con) x

-- match x { []: n ; k: v }
-- -----------------------------------------
-- ~x { []: n ; <>: λh. λt. v[k := h<>t] }
match d span x ms (([(cut -> Nil)], n) : ([(cut -> Var k i)], v) : _) = do
  n' <- desugarPats d span n
  v' <- desugarPats (d+2) span (bindVarByName k (Con (var d) (var (d+1))) v)
  let if_nil = lam d (map fst ms) n'
  let if_con = Lam (nam d) Nothing $ \_ -> Lam (nam (d+1)) Nothing $ \_ -> lam d (map fst ms) v'
  Done $ apps d (map snd ms) $ App (LstM if_nil if_con) x

-- match x { h<>t: c ; k: v }
-- ---------------------------------------
-- ~x { []: v[k := []] ; <>: λh. λt. c }
match d span x ms (([(cut -> Con h t)], c) : ([(cut -> Var k i)], v) : _) = do
  v' <- desugarPats d span (bindVarByName k Nil v)
  c' <- desugarPats (d+2) span c
  let if_nil = lam d (map fst ms) v'
  let if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) c'
  Done $ apps d (map snd ms) $ App (LstM if_nil if_con) x

-- match x { (): u }
-- -----------------
-- ~x { (): u }
-- Preserve location from the unit pattern: if the case pattern is a located
-- '()', then the generated λ{(): ...} inherits that original location.
match d span x ms (([p], u) : _) | isUnitPat p = do
  u' <- desugarPats d span u
  let mloc = unitPatLoc p
  let body = lam d (map fst ms) u'
  let uni  = maybe (UniM body) (\sp -> Loc sp (UniM body)) mloc
  Done $ apps d (map snd ms) $ App uni x
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
match d span x ms (([tup], p) : _) | isTupPat tup = do
  p' <- desugarPats (d+2) span p
  let mloc = tupPatLoc tup
  let (a, b) = tupPatFields tup
  let if_tup = Lam (patOf d a) Nothing $ \_ -> Lam (patOf (d+1) b) Nothing $ \_ -> lam d (map fst ms) p'
  let sigm = maybe (SigM if_tup) (\sp -> Loc sp (SigM if_tup)) mloc
  Done $ apps d (map snd ms) $ App sigm x
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
    tupPatFields _ = (Era, Era) -- Should never reach here due to guard

-- match x { @S1: b1 ; @S2: b2 ; ... ; k: d }
-- ------------------------------------------
-- ~x { @S1:b1 ; @S2:b2 ; ... ; d }
match d span x ms cs@(([(cut -> Sym _)], _) : _) = do
  (cBranches, defBranch) <- collect cs
  let enumMatch = case span of
        Span (0,0) (0,0) _ _ -> EnuM cBranches defBranch  -- noSpan case
        _                    -> Loc span (EnuM cBranches defBranch)
  Done $ apps d (map snd ms) $ App enumMatch x
  where
    collect :: [Case] -> Result ([(String, Term)], Term)
    collect [] = Done ([], Lam "_" Nothing $ \_ -> lam d (map fst ms) $ One)
    collect (([(cut -> Sym s)], rhs) : rest) = do
      rhs' <- desugarPats d span rhs
      (cs, def) <- collect rest
      Done ((s, lam d (map fst ms) rhs') : cs, def)
    collect (([(cut -> Var k _)], rhs) : _) = do
      rhs' <- desugarPats (d+1) span rhs
      Done ([], Lam k Nothing $ \_ -> lam d (map fst ms) rhs')
    collect (c:_) = Fail $ Unsupported span (Ctx []) (Just "Invalid pattern: invalid Sym case")

-- match x { &L{a,b}: s }
-- ---------------------------
-- ~ x { &L{,}: λa. λb. s }
match d span x ms (([(cut -> Sup l a b)], s) : _) = do
  s' <- desugarPats (d+2) span s
  let if_sup = Lam (patOf d a) Nothing $ \_ -> Lam (patOf (d+1) b) Nothing $ \_ -> lam d (map fst ms) s'
  Done $ apps d (map snd ms) $ App (SupM l if_sup) x

-- match x { Rfl: r }
-- ------------------
-- ~x { Rfl: r }
match d span x ms (([(cut -> Rfl)], r) : _) = do
  r' <- desugarPats d span r
  Done $ apps d (map snd ms) $ App (EqlM (lam d (map fst ms) r')) x

-- match x { k: body }
-- -------------------
-- body[k := x]
match d span x ms (([(cut -> Var k i)], body) : _) = do
  body' <- desugarPats d span (shove d ((k, x) : ms) body)
  Done $ lam d (map fst ms) body'

-- match x { }
-- -----------
-- λ{}
match d span x ms [] =
  let empMatch = case span of
        Span (0,0) (0,0) _ _ -> EmpM  -- Keep noSpan as raw EmpM
        _                    -> Loc span EmpM  -- Preserve location for error reporting
  in Done $ apps d (map snd ms) (App empMatch x)

-- Invalid pattern
-- match d span s ms cs = error $ "match - invalid pattern: " ++ show (d, s, ms, cs) ++ "\n" ++ show span
match d span s ms cs = Fail $ Unsupported span (Ctx []) (Just "Invalid pattern")

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
