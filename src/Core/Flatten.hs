{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}

-- Pattern Matching Flattener
-- ==========================
-- 
-- This algorithm converts pattern matching expressions with multiple 
-- scrutinees into nested case trees with single scrutinees. Example:
--
-- match x y
-- | 0n     0n          = X0
-- | (1n+x) 0n          = X1
-- | 0n     (1n+y)      = X2
-- | (1n+x) (1n+0n)     = X3
-- | (1n+x) (1n+(1n+z)) = X4
-- ------------------------- flatten
-- match x:
--   case 0n:
--     match y:
--       case 0n: X0
--       case 1+y: X2
--   case 1n+x:
--     match y:
--       case 0n: X1
--       case 1n+y_:
--         match y_:
--           case 0n: X3
--           case 1n+z: X4

module Core.Flatten where

import Data.List (nub, find)
import qualified Data.Map as M
import qualified Data.Set as S
import System.IO.Unsafe (unsafePerformIO)
import System.Exit

import Debug.Trace

import Core.Type
import Core.WHNF

-- Flattener
-- =========
-- Converts pattern-matches into if-lets, forcing the shape:
--   match x { with ... ; case @C: ... ; case x: ... }
-- After this transformation, the match will have exactly:
-- - 1 scrutinee
-- - 1 value case
-- - 1 default case
-- Outer scrutinees will be moved inside via 'with'.

flatten :: Int -> Book -> Term -> Term
flatten d book term = case term of
  (Var n i)     -> Var n i
  (Ref n)       -> Ref n
  (Sub t)       -> Sub (flatten d book t)
  (Fix n f)     -> Fix n (\x -> flatten (d+1) book (f x))
  (Let k t v f) -> Let k (fmap (flatten d book) t) (flatten d book v) (\x -> flatten (d+1) book (f x))
  Set           -> Set
  (Chk x t)     -> Chk (flatten d book x) (flatten d book t)
  Emp           -> Emp
  (EmpM x)      -> EmpM (flatten d book x)
  Uni           -> Uni
  One           -> One
  (UniM x f)    -> UniM (flatten d book x) (flatten d book f)
  Bit           -> Bit
  Bt0           -> Bt0
  Bt1           -> Bt1
  (BitM x f t)  -> BitM (flatten d book x) (flatten d book f) (flatten d book t)
  Nat           -> Nat
  Zer           -> Zer
  (Suc n)       -> Suc (flatten d book n)
  (NatM x z s)  -> NatM (flatten d book x) (flatten d book z) (flatten d book s)
  (Lst t)       -> Lst (flatten d book t)
  Nil           -> Nil
  (Con h t)     -> Con (flatten d book h) (flatten d book t)
  (LstM x n c)  -> LstM (flatten d book x) (flatten d book n) (flatten d book c)
  (Enu s)       -> Enu s
  (Sym s)       -> Sym s
  (EnuM x c e)  -> EnuM (flatten d book x) [(s, flatten d book t) | (s, t) <- c] (flatten d book e)
  (Sig a b)     -> Sig (flatten d book a) (flatten d book b)
  (Tup a b)     -> Tup (flatten d book a) (flatten d book b)
  (SigM x f)    -> SigM (flatten d book x) (flatten d book f)
  (All a b)     -> All (flatten d book a) (flatten d book b)
  (Lam n t f)   -> Lam n (fmap (flatten d book) t) (\x -> flatten (d+1) book (f x))
  (App f x)     -> App (flatten d book f) (flatten d book x)
  (Eql t a b)   -> Eql (flatten d book t) (flatten d book a) (flatten d book b)
  Rfl           -> Rfl
  (EqlM x f)    -> EqlM (flatten d book x) (flatten d book f)
  (Met i t x)   -> Met i (flatten d book t) (map (flatten d book) x)
  (Ind t)       -> Ind (flatten d book t)
  (Frz t)       -> Frz (flatten d book t)
  Era           -> Era
  (Sup l a b)   -> Sup (flatten d book l) (flatten d book a) (flatten d book b)
  (SupM x l f)  -> SupM (flatten d book x) (flatten d book l) (flatten d book f)
  (Frk l a b)   -> Frk (flatten d book l) (flatten d book a) (flatten d book b)
  (Num t)       -> Num t
  (Val v)       -> Val v
  (Op2 o a b)   -> Op2 o (flatten d book a) (flatten d book b)
  (Op1 o a)     -> Op1 o (flatten d book a)
  (Pri p)       -> Pri p
  (Log s x)     -> Log (flatten d book s) (flatten d book x)
  (Loc s t)     -> Loc s (flatten d book t)
  (Rwt a b x)   -> Rwt (flatten d book a) (flatten d book b) (flatten d book x)
  (Pat s m c)   -> simplify d $ flattenPat d book (Pat s m c)

isVarCol :: [Case] -> Bool
isVarCol []                        = True
isVarCol (((cut->Var _ _):_,_):cs) = isVarCol cs
isVarCol _                         = False

flattenPat :: Int -> Book -> Term -> Term
flattenPat d book pat =
  -- trace ("FLATTEN: " ++ show pat) $
  flattenPatGo d book pat where
    flattenPatGo d book pat@(Pat (s:ss) ms css@((((cut->Var k i):ps),rhs):cs)) | isVarCol css =
      -- trace (">> var: " ++ show pat) $
      flatten d book $ Pat ss ms (joinVarCol (d+1) book s (((Var k i:ps),rhs):cs))
      -- flatten d book $ Pat ss (ms++[(k,s)]) (joinVarCol (d+1) (Var k 0) (((Var k i:ps),rhs):cs))
    flattenPatGo d book pat@(Pat (s:ss) ms cs@((((cut->p):_),_):_)) =
      -- trace (">> ctr: " ++ show p ++ " " ++ show pat
          -- ++ "\n>> - picks: " ++ show picks
          -- ++ "\n>> - drops: " ++ show drops) $
      Pat [s] moves [([ct], flatten (d+length fs) book picks), ([var d], flatten (d+1) book drops)] where
        (ct,fs) = ctrOf d p
        (ps,ds) = peelCtrCol d book ct cs
        moves   = ms
        -- moves   = ms ++ map (\ (s,i) -> (patOf (d+i) s, s)) (zip ss [0..])
        picks   = Pat (fs   ++ ss) ms ps
        drops   = Pat (var d : ss) ms ds
    flattenPatGo d book pat@(Pat [] ms (([],rhs):cs)) =
      flatten d book rhs
    flattenPatGo d book (Loc l t) =
      Loc l (flattenPat d book t)
    flattenPatGo d book pat =
      pat

-- Converts an all-variable column to a 'with' statement
-- match x y { case x0 @A: F(x0) ; case x1 @B: F(x1) }
-- --------------------------------------------------- joinVarCol k
-- match y { with k=x case @A: F(k) ; case @B: F(k) }
joinVarCol :: Int -> Book -> Term -> [Case] -> [Case]
joinVarCol d book k ((((cut->Var j _):ps),rhs):cs) = (ps, subst j k rhs) : joinVarCol d book k cs
joinVarCol d book k ((((cut->ctr    ):ps),rhs):cs) = error "redundant pattern"
joinVarCol d book k cs                             = cs

-- Peels a constructor layer from a column
-- match x y:
--   case @Z{}      @A: A
--   case @S{@Z}    @B: B
--   case @S{@S{p}} @C: C(p)
-- ------------------------- peel @Z , peel @S{k}
-- match x:
--   with y
--   case @Z: # ↓ peel @Z
--     match y:
--       case @A: A
--   case @S{k}: # ↓ peel @S{k}
--     match k y:
--       case @Z    @B: B
--       case @S{p} @C: C(p)
peelCtrCol :: Int -> Book -> Term -> [Case] -> ([Case],[Case])
peelCtrCol d book (cut->k) ((((cut->p):ps),rhs):cs) = 
  -- trace (">> peel " ++ show k ++ " ~ " ++ show p) $
  case (k,p) of
    (Zer      , Zer    )   -> ((ps, rhs) : picks , drops)
    (Zer      , Var k _)   -> ((ps, subst k Zer rhs) : picks , ((p:ps),rhs) : drops)
    (Suc _    , Suc x  )   -> (((x:ps), rhs) : picks , drops)
    (Suc _    , Var k _)   -> (((Var k 0:ps), subst k (Suc (Var k 0)) rhs) : picks , ((p:ps),rhs) : drops)
    (Bt0      , Bt0    )   -> ((ps, rhs) : picks , drops)
    (Bt0      , Var k _)   -> ((ps, subst k Bt0 rhs) : picks , ((p:ps),rhs) : drops)
    (Bt1      , Bt1    )   -> ((ps, rhs) : picks , drops)
    (Bt1      , Var k _)   -> ((ps, subst k Bt1 rhs) : picks , ((p:ps),rhs) : drops)
    (Nil      , Nil    )   -> ((ps, rhs) : picks , drops)
    (Nil      , Var k _)   -> ((ps, subst k Nil rhs) : picks , ((p:ps),rhs) : drops)
    (Con _ _  , Con h t)   -> (((h:t:ps), rhs) : picks , drops)
    (Con _ _  , Var k _)   -> (((Var (k++"h") 0:Var (k++"t") 0:ps), subst k (Con (Var (k++"h") 0) (Var (k++"t") 0)) rhs) : picks , ((p:ps),rhs) : drops)
    (One      , One    )   -> ((ps, rhs) : picks , drops)
    (One      , Var k _)   -> ((ps, subst k One rhs) : picks , ((p:ps),rhs) : drops)
    (Tup _ _  , Tup a b)   -> (((a:b:ps), rhs) : picks , drops)
    (Tup _ _  , Var k _)   -> (((Var (k++"x") 0:Var (k++"y") 0:ps), subst k (Tup (Var (k++"x") 0) (Var (k++"y") 0)) rhs) : picks , ((p:ps),rhs) : drops)
    (Sym s    , Sym s' )
               | s == s'   -> ((ps, rhs) : picks , drops)
    (Sym s    , Var k _)   -> ((ps, subst k (Sym s) rhs) : picks , ((p:ps),rhs) : drops)
    (Rfl      , Rfl    )   -> ((ps, rhs) : picks , drops)
    (Rfl      , Var k _)   -> ((ps, subst k Rfl rhs) : picks , ((p:ps),rhs) : drops)
    (Sup l _ _, Sup r a b) -> (((a:b:ps), rhs) : picks , drops)
    (Sup l _ _, Var k _)   -> (((Var (k++"a") 0:Var (k++"b") 0:ps), subst k (Sup l (Var (k++"a") 0) (Var (k++"b") 0)) rhs) : picks , ((p:ps),rhs) : drops)
    (Var _ _  , p      )   -> unsupported
    (k        , App f x)   -> callPatternSugar d book k f x p ps rhs cs
    x                      -> (picks , ((p:ps),rhs) : drops)
  where (picks, drops) = peelCtrCol d book k cs
peelCtrCol d book k cs = (cs,cs)

-- Allows using a function call in a pattern. Example:
--   case Foo(p): return 1n + add(p,b)
--   (where 'Foo' is a user-defined function)
callPatternSugar :: Int -> Book -> Term -> Term -> Term -> Term -> [Term] -> Term -> [Case] -> ([Case],[Case])
callPatternSugar d book k f x p ps rhs cs =
  peelCtrCol d book k (((exp:ps),rhs):cs)
  where (fn,xs) = collectApps (App f x)  []
        exp     = normal d book $ foldl App ref xs
        ref     = case fn of
          Ref k     -> Ref k
          Var k _   -> Ref k
          otherwise -> error $ "invalid-call-pattern:" ++ show (App f x)

-- Simplify
-- ========
-- Removes redundant matches, adjusts form

-- >> match _x7 M{ case (False): () case (_x8): match _x8 M{ } }

-- Substitutes a move list into an expression
shove :: Int -> [Move] -> Term -> Term
shove d ms term = foldr (\ (k,v) x -> subst k v x) term ms 

simplify :: Int -> Term -> Term
simplify d (Pat ss ms cs) =
  case Pat ss ms (map (\ (p, c) -> (p, simplify d c)) cs) of
    pat@(Pat [] ms (([],rhs):cs)) ->
      simplify d (shove d ms rhs)
    pat@(Pat ss ms cs) -> Pat ss ms (merge d cs)
simplify d (Loc l t) = Loc l (simplify d t)
simplify d pat       = pat

-- Merges redundant case-match chains into parent
-- ... case x: match x { case A:A ; case B:B ... } ...
-- --------------------------------------------------- simplify
-- ... case A:A ; case B:B ...
merge :: Int -> [Case] -> [Case]
merge d (([Var x _], (Pat [Var x' _] ms cs')) : cs)
                | x == x' = csA ++ csB
                where csA = map (\ (p, rhs) -> (p, shove d ms rhs)) cs'
                      csB = merge d cs
merge d ((p,rhs):cs) = (p, rhs) : merge d cs
merge d []           = []

-- match { with x=A ... case: F(x,...) ... }
-- ----------------------------------------- simplify-decay
-- F(A,...)
decay :: Int -> Term -> Term
decay d (Pat [] ms (([],rhs):cs)) = simplify d (shove d ms rhs)
decay d pat                       = pat

-- UnPat
-- =====
-- Converts all Pats to native expression-based matches.

unpat :: Int -> Term -> Term
unpat d (Var n i)       = Var n i
unpat d (Ref n)         = Ref n
unpat d (Sub t)         = Sub (unpat d t)
unpat d (Fix n f)       = Fix n (\x -> unpat (d+1) (f x))
unpat d (Let k t v f)   = Let k (fmap (unpat d) t) (unpat d v) (\x -> unpat (d+1) (f x))
unpat d Set             = Set
unpat d (Chk x t)       = Chk (unpat d x) (unpat d t)
unpat d Emp             = Emp
unpat d (EmpM x)        = EmpM (unpat d x)
unpat d Uni             = Uni
unpat d One             = One
unpat d (UniM x f)      = UniM (unpat d x) (unpat d f)
unpat d Bit             = Bit
unpat d Bt0             = Bt0
unpat d Bt1             = Bt1
unpat d (BitM x f t)    = BitM (unpat d x) (unpat d f) (unpat d t)
unpat d Nat             = Nat
unpat d Zer             = Zer
unpat d (Suc n)         = Suc (unpat d n)
unpat d (NatM x z s)    = NatM (unpat d x) (unpat d z) (unpat d s)
unpat d (Lst t)         = Lst (unpat d t)
unpat d Nil             = Nil
unpat d (Con h t)       = Con (unpat d h) (unpat d t)
unpat d (LstM x n c)    = LstM (unpat d x) (unpat d n) (unpat d c)
unpat d (Enu s)         = Enu s
unpat d (Sym s)         = Sym s
unpat d (EnuM x c e)    = EnuM (unpat d x) [(s, unpat d t) | (s, t) <- c] (unpat d e)
unpat d (Sig a b)       = Sig (unpat d a) (unpat d b)
unpat d (Tup a b)       = Tup (unpat d a) (unpat d b)
unpat d (SigM x f)      = SigM (unpat d x) (unpat d f)
unpat d (All a b)       = All (unpat d a) (unpat d b)
unpat d (Lam n t f)     = Lam n (fmap (unpat d) t) (\x -> unpat (d+1) (f x))
unpat d (App f x)       = App (unpat d f) (unpat d x)
unpat d (Eql t a b)     = Eql (unpat d t) (unpat d a) (unpat d b)
unpat d Rfl             = Rfl
unpat d (EqlM x f)      = EqlM (unpat d x) (unpat d f)
unpat d (Met i t x)     = Met i (unpat d t) (map (unpat d) x)
unpat d (Ind t)         = Ind (unpat d t)
unpat d (Frz t)         = Frz (unpat d t)
unpat d Era             = Era
unpat d (Sup l a b)     = Sup (unpat d l) (unpat d a) (unpat d b)
unpat d (SupM x l f)    = SupM (unpat d x) (unpat d l) (unpat d f)
unpat d (Frk l a b)     = Frk (unpat d l) (unpat d a) (unpat d b)
unpat d (Num t)         = Num t
unpat d (Val v)         = Val v
unpat d (Op2 o a b)     = Op2 o (unpat d a) (unpat d b)
unpat d (Op1 o a)       = Op1 o (unpat d a)
unpat d (Pri p)         = Pri p
unpat d (Log s x)       = Log (unpat d s) (unpat d x)
unpat d (Loc s t)       = Loc s (unpat d t)
unpat d (Rwt a b f)     = Rwt (unpat d a) (unpat d b) (unpat d f)
unpat d (Pat [s] ms cs) = match d s ms cs
unpat d (Pat ss  ms []) = One
unpat d (Pat ss  ms cs) = error "unpat: multiple scrutinees after flattening"

match :: Int -> Term -> [Move] -> [Case] -> Term

-- match x { 0n: z ; 1n+p: s }
-- ---------------------------
-- ~x { 0n: z ; 1n+: λp. s }
match d x ms (([(cut -> Zer)], z) : ([(cut -> Suc p)], s) : _) =
  apps d (map snd ms) $ NatM x if_zer if_suc
  where if_zer = lam d (map fst ms) $ unpat d z
        if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) $ unpat (d+1) s

-- match x { 1n+p: s ; 0n: z }
-- ---------------------------
-- ~x { 0n: z ; 1n+: λp. s }
match d x ms (([(cut -> Suc p)], s) : ([(cut -> Zer)], z) : _) =
  apps d (map snd ms) $ NatM x if_zer if_suc
  where if_zer = lam d (map fst ms) $ unpat d z
        if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) $ unpat (d+1) s

-- match x { 0n: z ; k: v }
-- --------------------------------------
-- ~x { 0n: z ; 1n+: λk. v[k := 1n+k] }
match d x ms (([(cut -> Zer)], z) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ NatM x if_zer if_suc
  where if_zer = lam d (map fst ms) $ unpat d z
        if_suc = Lam k (Just Nat) $ \x -> lam d (map fst ms) $ unpat (d+1) (subst k (Suc (Var k 0)) v)

-- match x { 1n+p: s ; k: v }
-- ------------------------------------
-- ~x { 0n: v[k := 0n] ; 1n+: λp. s }
match d x ms (([(cut -> Suc p)], s) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ NatM x if_zer if_suc
  where if_zer = lam d (map fst ms) $ unpat d (subst k Zer v)
        if_suc = Lam (patOf d p) (Just Nat) $ \x -> lam d (map fst ms) $ unpat (d+1) s

-- match x { False: f ; True: t }
-- ------------------------------
-- ~x { False: f ; True: t }
match d x ms (([(cut -> Bt0)], f) : ([(cut -> Bt1)], t) : _) =
  apps d (map snd ms) $ BitM x (lam d (map fst ms) $ unpat d f) (lam d (map fst ms) $ unpat d t)

-- match x { True: t ; False: f }
-- ------------------------------
-- ~x { False: f ; True: t }
match d x ms (([(cut -> Bt1)], t) : ([(cut -> Bt0)], f) : _) =
  apps d (map snd ms) $ BitM x (lam d (map fst ms) $ unpat d f) (lam d (map fst ms) $ unpat d t)

-- match x { False: f ; k: v }
-- --------------------------------------
-- ~x { False: f ; True: v[k := True] }
match d x ms (([(cut -> Bt0)], f) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ BitM x (lam d (map fst ms) $ unpat d f) (lam d (map fst ms) $ unpat d (subst k Bt1 v))

-- match x { True: t ; k: v }
-- ---------------------------------------
-- ~x { False: v[k := False] ; True: t }
match d x ms (([(cut -> Bt1)], t) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ BitM x (lam d (map fst ms) $ unpat d (subst k Bt0 v)) (lam d (map fst ms) $ unpat d t)

-- match x { []: n ; h<>t: c }
-- ------------------------------
-- ~x { []: n ; <>: λh. λt. c }
match d x ms (([(cut -> Nil)], n) : ([(cut -> Con h t)], c) : _) =
  apps d (map snd ms) $ LstM x if_nil if_con
  where if_nil = lam d (map fst ms) $ unpat d n
        if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) $ unpat (d+2) c

-- match x { h<>t: c ; []: n }
-- ------------------------------
-- ~x { []: n ; <>: λh. λt. c }
match d x ms (([(cut -> Con h t)], c) : ([(cut -> Nil)], n) : _) =
  apps d (map snd ms) $ LstM x if_nil if_con
  where if_nil = lam d (map fst ms) $ unpat d n
        if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) $ unpat (d+2) c

-- match x { []: n ; k: v }
-- -----------------------------------------
-- ~x { []: n ; <>: λh. λt. v[k := h<>t] }
match d x ms (([(cut -> Nil)], n) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ LstM x if_nil if_con
  where if_nil = lam d (map fst ms) $ unpat d n
        if_con = Lam (nam d) Nothing $ \_ -> Lam (nam (d+1)) Nothing $ \_ -> lam d (map fst ms) $ unpat (d+2) (subst k (Con (var d) (var (d+1))) v)

-- match x { h<>t: c ; k: v }
-- ---------------------------------------
-- ~x { []: v[k := []] ; <>: λh. λt. c }
match d x ms (([(cut -> Con h t)], c) : ([(cut -> Var k i)], v) : _) =
  apps d (map snd ms) $ LstM x if_nil if_con
  where if_nil = lam d (map fst ms) $ unpat d (subst k Nil v)
        if_con = Lam (patOf d h) Nothing $ \_ -> Lam (patOf (d+1) t) Nothing $ \_ -> lam d (map fst ms) $ unpat (d+2) c

-- match x { (): u }
-- -----------------
-- ~x { (): u }
match d x ms cs@(([(cut -> One)], u) : _) =
  apps d (map snd ms) $ UniM x (lam d (map fst ms) $ unpat d u)

-- match x { (a,b): p }
-- --------------------
-- ~x { (,): λa. λb. p }
match d x ms (([(cut -> Tup a b)], p) : _) =
  apps d (map snd ms) $ SigM x if_tup
  where if_tup = Lam (patOf d a) Nothing $ \_ -> Lam (patOf (d+1) b) Nothing $ \_ -> lam d (map fst ms) $ unpat (d+2) p

-- match x { @S1: b1 ; @S2: b2 ; ... ; k: d }
-- ------------------------------------------
-- ~x { @S1:b1 ; @S2:b2 ; ... ; d }
match d x ms cs@(([(cut -> Sym _)], _) : _) =
  let (cBranches, defBranch) = collect cs
  in apps d (map snd ms) $ EnuM x cBranches defBranch
  where
    collect :: [Case] -> ([(String, Term)], Term)
    collect [] = ([], Lam "_" Nothing $ \_ -> lam d (map fst ms) $ One)
    collect (([(cut -> Sym s)], rhs) : rest) =
      let (cs, def) = collect rest
      in ((s, lam d (map fst ms) $ unpat d rhs) : cs, def)
    collect (([(cut -> Var k _)], rhs) : _) =
      ([], Lam k Nothing $ \_ -> lam d (map fst ms) $ unpat (d+1) rhs)
    collect (c:_) = error $ "match:invalid-Sym-case:" ++ show c

-- match x { {==}: r }
-- --------------------
-- ~x { {==}: r }
match d x ms (([(cut -> Rfl)], r) : _) =
  apps d (map snd ms) $ EqlM x (lam d (map fst ms) $ unpat d r)

-- match x { &L{a,b}: s }
-- ---------------------------
-- ~ x { &L{,}: λa. λb. s }
match d x ms (([(cut -> Sup l a b)], s) : _) =
  apps d (map snd ms) $ SupM x l if_sup
  where if_sup = Lam (patOf d a) Nothing $ \_ -> Lam (patOf (d+1) b) Nothing $ \_ -> lam d (map fst ms) $ unpat (d+2) s

-- match x { k: body }
-- -------------------
-- body[k := x]
match d x ms (([(cut -> Var k i)], body) : _) =
  lam d (map fst ms) $ unpat d (shove d ((k, x) : ms) body)

-- match x { }
-- -----------
-- λ{}
match d x ms [] =
  apps d (map snd ms) (EmpM x)

-- Invalid pattern
match d s ms cs = error $ "match - invalid pattern: " ++ show (d, s, ms, cs)

-- Helper function to create lambda abstractions
lam :: Int -> [Name] -> Term -> Term
lam d []     t = t
lam d (k:ks) t = Lam k Nothing $ \_ -> lam (d+1) ks t

-- UnFrk
-- =====
-- Removes all Frks from a Term, as follows:
--   fork L: A else: B (with ctx=[a,b,...])
--   --------------------------------------
--   &L{a0,a1} = a
--   &L{b0,b1} = b
--   ...
--   &L{A[a<-a0, b<-b0, ...], B[a<-a1,b<-b1, ...]}
-- That is, whenever a 'Frk L a b' constructor is found, we:
-- 1. Superpose each variable of the context (using a SupM with label L)
-- 2. Return a Sup of a and b, where the context on each side is entirely
--    replaced by the corresponding side of the forked variable

unfrk :: Int -> Term -> Term
unfrk d term = unfrkGo d [] term

unfrkGo :: Int -> [(Name, Int)] -> Term -> Term
unfrkGo d ctx (Var n i)     = Var n i
unfrkGo d ctx (Ref n)       = Ref n
unfrkGo d ctx (Sub t)       = Sub (unfrkGo d ctx t)
unfrkGo d ctx (Fix n f)     = Fix n (\x -> unfrkGo (d+1) ((n,d):ctx) (f x))
unfrkGo d ctx (Let k t v f) = Let k (fmap (unfrkGo d ctx) t) (unfrkGo d ctx v) (\x -> unfrkGo (d+1) ((k,d):ctx) (f x))
unfrkGo d ctx Set           = Set
unfrkGo d ctx (Chk x t)     = Chk (unfrkGo d ctx x) (unfrkGo d ctx t)
unfrkGo d ctx Emp           = Emp
unfrkGo d ctx (EmpM x)      = EmpM (unfrkGo d ctx x)
unfrkGo d ctx Uni           = Uni
unfrkGo d ctx One           = One
unfrkGo d ctx (UniM x f)    = UniM (unfrkGo d ctx x) (unfrkGo d ctx f)
unfrkGo d ctx Bit           = Bit
unfrkGo d ctx Bt0           = Bt0
unfrkGo d ctx Bt1           = Bt1
unfrkGo d ctx (BitM x f t)  = BitM (unfrkGo d ctx x) (unfrkGo d ctx f) (unfrkGo d ctx t)
unfrkGo d ctx Nat           = Nat
unfrkGo d ctx Zer           = Zer
unfrkGo d ctx (Suc n)       = Suc (unfrkGo d ctx n)
unfrkGo d ctx (NatM x z s)  = NatM (unfrkGo d ctx x) (unfrkGo d ctx z) (unfrkGo d ctx s)
unfrkGo d ctx (Lst t)       = Lst (unfrkGo d ctx t)
unfrkGo d ctx Nil           = Nil
unfrkGo d ctx (Con h t)     = Con (unfrkGo d ctx h) (unfrkGo d ctx t)
unfrkGo d ctx (LstM x n c)  = LstM (unfrkGo d ctx x) (unfrkGo d ctx n) (unfrkGo d ctx c)
unfrkGo d ctx (Enu s)       = Enu s
unfrkGo d ctx (Sym s)       = Sym s
unfrkGo d ctx (EnuM x c e)  = EnuM (unfrkGo d ctx x) [(s, unfrkGo d ctx t) | (s, t) <- c] (unfrkGo d ctx e)
unfrkGo d ctx (Sig a b)     = Sig (unfrkGo d ctx a) (unfrkGo d ctx b)
unfrkGo d ctx (Tup a b)     = Tup (unfrkGo d ctx a) (unfrkGo d ctx b)
unfrkGo d ctx (SigM x f)    = SigM (unfrkGo d ctx x) (unfrkGo d ctx f)
unfrkGo d ctx (All a b)     = All (unfrkGo d ctx a) (unfrkGo d ctx b)
unfrkGo d ctx (Lam n t f)   = Lam n (fmap (unfrkGo d ctx) t) (\x -> unfrkGo (d+1) ((n,d):ctx) (f x))
unfrkGo d ctx (App f x)     = App (unfrkGo d ctx f) (unfrkGo d ctx x)
unfrkGo d ctx (Eql t a b)   = Eql (unfrkGo d ctx t) (unfrkGo d ctx a) (unfrkGo d ctx b)
unfrkGo d ctx Rfl           = Rfl
unfrkGo d ctx (EqlM x f)    = EqlM (unfrkGo d ctx x) (unfrkGo d ctx f)
unfrkGo d ctx (Met i t x)   = Met i (unfrkGo d ctx t) (map (unfrkGo d ctx) x)
unfrkGo d ctx (Ind t)       = Ind (unfrkGo d ctx t)
unfrkGo d ctx (Frz t)       = Frz (unfrkGo d ctx t)
unfrkGo d ctx Era           = Era
unfrkGo d ctx (Sup l a b)   = Sup (unfrkGo d ctx l) (unfrkGo d ctx a) (unfrkGo d ctx b)
unfrkGo d ctx (SupM x l f)  = SupM (unfrkGo d ctx x) (unfrkGo d ctx l) (unfrkGo d ctx f)
unfrkGo d ctx (Frk l a b)   = unfrkFrk d ctx l a b
unfrkGo d ctx (Num t)       = Num t
unfrkGo d ctx (Val v)       = Val v
unfrkGo d ctx (Op2 o a b)   = Op2 o (unfrkGo d ctx a) (unfrkGo d ctx b)
unfrkGo d ctx (Op1 o a)     = Op1 o (unfrkGo d ctx a)
unfrkGo d ctx (Pri p)       = Pri p
unfrkGo d ctx (Log s x)     = Log (unfrkGo d ctx s) (unfrkGo d ctx x)
unfrkGo d ctx (Loc s t)     = Loc s (unfrkGo d ctx t)
unfrkGo d ctx (Rwt a b x)   = Rwt (unfrkGo d ctx a) (unfrkGo d ctx b) (unfrkGo d ctx x)
unfrkGo d ctx (Pat s m c)   = Pat (map (unfrkGo d ctx) s) [(k, unfrkGo d ctx v) | (k,v) <- m] [(p, unfrkGo d (ctxCs p) f) | (p, f) <- c]
  where
    ctxCs  p = ctx ++ map (\(k,v) -> (k, d)) m ++ ctxPat p
    ctxPat p = map (\k -> (k, d)) (S.toList (S.unions (map (freeVars S.empty) p)))

unfrkFrk :: Int -> [(Name, Int)] -> Term -> Term -> Term -> Term
unfrkFrk d ctx l a b = buildSupMs vars where
  vars =  shadowCtx (filter (\x -> fst x `S.member` free) (reverse ctx))
  free = case cut l of
    -- 'l' must be a non-superposed U64 so we can remove it from the forked vars as a (reasonable) optimization.
    Var n _ -> S.delete n (freeVars S.empty a `S.union` freeVars S.empty b)
    _       -> freeVars S.empty a `S.union` freeVars S.empty b
  -- Build nested SupM matches for each context variable
  buildSupMs :: [(Name, Int)] -> Term
  buildSupMs [] = Sup l a' b' where
    ls = [(n, Var (n++"0") 0) | (n, _) <- vars]
    rs = [(n, Var (n++"1") 0) | (n, _) <- vars]
    a' = substMany ls (unfrkGo d ctx a)
    b' = substMany rs (unfrkGo d ctx b)
  -- For each variable, create a SupM that binds the superposed versions
  buildSupMs ((n,d):rest) =
    SupM (Var n d) l $
    Lam (n++"0") Nothing $ \_ ->
    Lam (n++"1") Nothing $ \_ ->
    buildSupMs rest
  -- Removes repeated (shadowed) vars from the context
  shadowCtx ((n,d):ctx) =
    if n `elem` (map fst ctx)
      then shadowCtx ctx
      else (n,d) : shadowCtx ctx
  shadowCtx [] = []

-- Helpers
-- -------

-- Injects lambdas after skipping n lambdas
lams :: Int -> [Name] -> Term -> Term
lams d (k:ks) t = Lam k Nothing $ \_ -> lams (d+1) ks t
lams d []     t = t

-- Applies n arguments to a value
apps :: Int -> [Term] -> Term -> Term
apps d ms t = foldl (\t x -> App t x) t ms

-- Creates a fresh name at given depth
nam :: Int -> String
nam d = "_x" ++ show d

-- Creates a fresh variable at given depth
var :: Int -> Term
var d = Var (nam d) d

-- Creates a fresh pattern at given depth
pat :: Int -> Term -> Term
pat d f = Var (patOf d f) d

-- Gets a var name, or creates a fresh one
patOf :: Int -> Term -> String
patOf d (cut->Var k i) = k
patOf d p              = nam d

-- Returns a single-layer constructor, replacing fields by pattern variables
ctrOf :: Int -> Term -> (Term, [Term])
ctrOf d Zer         = (Zer , [])
ctrOf d (Suc p)     = (Suc (pat d p), [pat d p])
ctrOf d Bt0         = (Bt0 , [])
ctrOf d Bt1         = (Bt1 , [])
ctrOf d Nil         = (Nil , [])
ctrOf d (Con h t)   = (Con (pat d h) (pat (d+1) t), [pat d h, pat (d+1) t])
ctrOf d One         = (One , [])
ctrOf d (Tup a b)   = (Tup (pat d a) (pat (d+1) b), [pat d a, pat (d+1) b])
ctrOf d (Sym s)     = (Sym s, [])
ctrOf d Rfl         = (Rfl , [])
ctrOf d (Sup l a b) = (Sup l (pat d a) (pat (d+1) b), [pat d a, pat (d+1) b])
ctrOf d x           = (var d , [var d])

-- Subst a var for a value in a term
subst :: Name -> Term -> Term -> Term
subst name val term = go name val term where
  go name val term = case term of
    Var k _     -> if k == name then val else term
    Ref k       -> Ref k
    Sub t       -> Sub (go name val t)
    Fix k f     -> if k == name then term else Fix k (\x -> go name val (f x))
    Let k t v f -> if k == name then term else Let k (fmap (go name val) t) (go name val v) (\x -> go name val (f x))
    Chk x t     -> Chk (go name val x) (go name val t)
    Set         -> Set
    Emp         -> Emp
    EmpM x      -> EmpM (go name val x)
    Uni         -> Uni
    One         -> One
    UniM x f    -> UniM (go name val x) (go name val f)
    Bit         -> Bit
    Bt0         -> Bt0
    Bt1         -> Bt1
    BitM x f t  -> BitM (go name val x) (go name val f) (go name val t)
    Nat         -> Nat
    Zer         -> Zer
    Suc n       -> Suc (go name val n)
    NatM x z s  -> NatM (go name val x) (go name val z) (go name val s)
    Lst t       -> Lst (go name val t)
    Nil         -> Nil
    Con h t     -> Con (go name val h) (go name val t)
    LstM x n c  -> LstM (go name val x) (go name val n) (go name val c)
    Enu s       -> Enu s
    Sym s       -> Sym s
    EnuM x c e  -> EnuM (go name val x) [(s, go name val t) | (s, t) <- c] (go name val e)
    Sig a b     -> Sig (go name val a) (go name val b)
    Tup a b     -> Tup (go name val a) (go name val b)
    SigM x f    -> SigM (go name val x) (go name val f)
    All a b     -> All (go name val a) (go name val b)
    Lam k t f   -> if k == name then term else Lam k (fmap (go name val) t) (\x -> go name val (f x))
    App f x     -> App (go name val f) (go name val x)
    Eql t a b   -> Eql (go name val t) (go name val a) (go name val b)
    Rfl         -> Rfl
    EqlM x f    -> EqlM (go name val x) (go name val f)
    Met i t x   -> Met i (go name val t) (map (go name val) x)
    Ind t       -> Ind (go name val t)
    Frz t       -> Frz (go name val t)
    Era         -> Era
    Sup l a b   -> Sup (go name val l) (go name val a) (go name val b)
    SupM x l f  -> SupM (go name val x) (go name val l) (go name val f)
    Frk l a b   -> Frk (go name val l) (go name val a) (go name val b)
    Num t       -> Num t
    Val v       -> Val v
    Op2 o a b   -> Op2 o (go name val a) (go name val b)
    Op1 o a     -> Op1 o (go name val a)
    Pri p       -> Pri p
    Log s x     -> Log (go name val s) (go name val x)
    Loc s t     -> Loc s (go name val t)
    Rwt a b x   -> Rwt (go name val a) (go name val b) (go name val x)
    Pat s m c   -> Pat (map (go name val) s) m (map cse c)
      where cse (pats, rhs) = (map (go name val) pats, go name val rhs)

-- Helper to substitute multiple variables at once
substMany :: [(Name, Term)] -> Term -> Term
substMany subs term = foldr (\ (n,v) t -> subst n v t) term subs

-- -- Substitutes multiple variables in a term
-- substCtx :: [(Name, Term)] -> Term -> Term
-- substCtx []         term = term
-- substCtx ((n,v):xs) term = substCtx xs (subst n v term)

unsupported :: a
unsupported = unsafePerformIO $ do
  putStrLn $ "Unsupported pattern-match shape."
  putStrLn $ "Support for it will be added in a future update."
  exitFailure
