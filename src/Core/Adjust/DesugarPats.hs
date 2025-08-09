{-./../Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Adjust.DesugarPats where

-- Pattern Desugaring
-- ==================
-- Converts all Pats to native expression-based matches.

import Core.Bind
import Core.Show
import Core.Type
import Core.WHNF
import qualified Data.Set as S

desugarPats :: Int -> Span -> Book -> Term -> Term
desugarPats d span book (Var n i)       = Var n i
desugarPats d span book (Ref n i)       = Ref n i
desugarPats d span book (Sub t)         = Sub (desugarPats d span book t)
desugarPats d span book (Fix n f)       = Fix n (\x -> desugarPats (d+1) span book (f x))
desugarPats d span book (Let k t v f)   = Let k (fmap (desugarPats d span book) t) (desugarPats d span book v) (\x -> desugarPats (d+1) span book (f x))
desugarPats d span book (Use k v f)     = Use k (desugarPats d span book v) (\x -> desugarPats (d+1) span book (f x))
desugarPats d span book Set             = Set
desugarPats d span book (Chk x t)       = Chk (desugarPats d span book x) (desugarPats d span book t)
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
desugarPats d span book (ADT n ts)      = ADT n (map (desugarPats d span book) ts)
desugarPats d span book (Ctr n ts)      = Ctr n (map (desugarPats d span book) ts)
desugarPats d span book (ADTM n cs df)  = ADTM n [(c, desugarPats d span book t) | (c, t) <- cs] (fmap (desugarPats d span book) df)
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
match d span book x ms cs@(([(cut -> One)], u) : _) =
  apps d (map snd ms) $ App (UniM (lam d (map fst ms) $ desugarPats d span book u)) x

-- match x { (a,b): p }
-- --------------------
-- ~x { (,): λa. λb. p }
match d span book x ms (([(cut -> Tup a b)], p) : _) =
  apps d (map snd ms) $ App (SigM if_tup) x
  where if_tup = Lam (patOf d a) Nothing $ \_ -> Lam (patOf (d+1) b) Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+2) span book p

-- match x { K{args}: body ; ... }  (ADT constructors)
-- ----------------------------------------------------
-- ~x { K{}: λargs. body ; ... }
match d span book x ms cs@(([(cut -> Ctr _ _)], _) : _) =
  let adt                       = getAdtName book (head cs)
      (ctrBranches, defBranch)  = collect cs
  in  apps d (map snd ms) $ App (ADTM adt ctrBranches defBranch) x
  where
    collect :: [Case] -> ([(Name,Term)], Maybe Term)
    collect [] = ([], Nothing)

    collect (([(cut -> Ctr c args)], rhs) : rest) =
      let (cs', def') = collect rest
          -- Extract field names from constructor arguments
          -- If args are variables, use their names; otherwise create fresh names
          fieldNames = zipWith (\arg idx -> patOf (d + idx) arg) args [0..]
          -- Create the body with lambdas for each field
          mkLams [] body depth = body
          mkLams (fname:fnames) body depth = Lam fname Nothing $ \_ -> mkLams fnames body (depth + 1)
          brTerm = lam d (map fst ms) $ mkLams fieldNames (desugarPats (d + length args) span book rhs) d
      in  ((c, brTerm) : cs', def')

    collect (([(cut -> Var k _)], rhs) : _) =
      let defTerm = Lam k Nothing $ \_ -> lam d (map fst ms) $ desugarPats (d+1) span book rhs
      in  ([], Just defTerm)

    collect _ =
      errorWithSpan span "Invalid pattern: invalid ADT constructor case"

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
-- match d span book s ms cs = error $ "match - invalid pattern: " ++ show (d, s, ms, cs) ++ "\n" ++ show span
match d span book s ms cs = errorWithSpan span "Invalid pattern."

-- Helper function to create lambda abstractions
lam :: Int -> [Name] -> Term -> Term
lam d []     t = t
lam d (k:ks) t = Lam k Nothing $ \_ -> lam (d+1) ks t

-- Applies n arguments to a value
apps :: Int -> [Term] -> Term -> Term
apps d ms t = foldl (\t x -> App t x) t ms

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
