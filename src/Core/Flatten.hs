{-./Type.hs-}

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
flatten d book (Var n i)    = Var n i
flatten d book (Ref n)      = Ref n
flatten d book (Sub t)      = Sub (flatten d book t)
flatten d book (Fix n f)    = Fix n (\x -> flatten (d+1) book (f x))
flatten d book (Let v f)    = Let (flatten d book v) (flatten d book f)
flatten d book Set          = Set
flatten d book (Chk x t)    = Chk (flatten d book x) (flatten d book t)
flatten d book Emp          = Emp
flatten d book (EmpM x)     = EmpM (flatten d book x)
flatten d book Uni          = Uni
flatten d book One          = One
flatten d book (UniM x f)   = UniM (flatten d book x) (flatten d book f)
flatten d book Bit          = Bit
flatten d book Bt0          = Bt0
flatten d book Bt1          = Bt1
flatten d book (BitM x f t) = BitM (flatten d book x) (flatten d book f) (flatten d book t)
flatten d book Nat          = Nat
flatten d book Zer          = Zer
flatten d book (Suc n)      = Suc (flatten d book n)
flatten d book (NatM x z s) = NatM (flatten d book x) (flatten d book z) (flatten d book s)
flatten d book (Lst t)      = Lst (flatten d book t)
flatten d book Nil          = Nil
flatten d book (Con h t)    = Con (flatten d book h) (flatten d book t)
flatten d book (LstM x n c) = LstM (flatten d book x) (flatten d book n) (flatten d book c)
flatten d book (Enu s)      = Enu s
flatten d book (Sym s)      = Sym s
flatten d book (EnuM x c e) = EnuM (flatten d book x) [(s, flatten d book t) | (s, t) <- c] (flatten d book e)
flatten d book (Sig a b)    = Sig (flatten d book a) (flatten d book b)
flatten d book (Tup a b)    = Tup (flatten d book a) (flatten d book b)
flatten d book (SigM x f)   = SigM (flatten d book x) (flatten d book f)
flatten d book (All a b)    = All (flatten d book a) (flatten d book b)
flatten d book (Lam n f)    = Lam n (\x -> flatten (d+1) book (f x))
flatten d book (App f x)    = App (flatten d book f) (flatten d book x)
flatten d book (Eql t a b)  = Eql (flatten d book t) (flatten d book a) (flatten d book b)
flatten d book Rfl          = Rfl
flatten d book (EqlM x f)   = EqlM (flatten d book x) (flatten d book f)
flatten d book (Met i t x)  = Met i (flatten d book t) (map (flatten d book) x)
flatten d book (Ind t)      = Ind (flatten d book t)
flatten d book (Frz t)      = Frz (flatten d book t)
flatten d book Era          = Era
flatten d book (Sup l a b)  = Sup l (flatten d book a) (flatten d book b)
flatten d book (Num t)      = Num t
flatten d book (Val v)      = Val v
flatten d book (Op2 o a b)  = Op2 o (flatten d book a) (flatten d book b)
flatten d book (Op1 o a)    = Op1 o (flatten d book a)
flatten d book (Pri p)      = Pri p
flatten d book (Loc s t)    = Loc s (flatten d book t)
flatten d book (Rwt a b x)  = Rwt (flatten d book a) (flatten d book b) (flatten d book x)
flatten d book (Pat s m c)  = simplify d $ flattenPat d book (Pat s m c)

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
      flattenPat d book rhs
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
    (Zer    , Zer    ) -> ((ps, rhs) : picks , drops)
    (Zer    , Var k _) -> ((ps, subst k Zer rhs) : picks , ((p:ps),rhs) : drops)
    (Suc _  , Suc x  ) -> (((x:ps), rhs) : picks , drops)
    (Suc _  , Var k _) -> (((Var k 0:ps), subst k (Suc (Var k 0)) rhs) : picks , ((p:ps),rhs) : drops)
    (Bt0    , Bt0    ) -> ((ps, rhs) : picks , drops)
    (Bt0    , Var k _) -> ((ps, subst k Bt0 rhs) : picks , ((p:ps),rhs) : drops)
    (Bt1    , Bt1    ) -> ((ps, rhs) : picks , drops)
    (Bt1    , Var k _) -> ((ps, subst k Bt1 rhs) : picks , ((p:ps),rhs) : drops)
    (Nil    , Nil    ) -> ((ps, rhs) : picks , drops)
    (Nil    , Var k _) -> ((ps, subst k Nil rhs) : picks , ((p:ps),rhs) : drops)
    (Con _ _, Con h t) -> (((h:t:ps), rhs) : picks , drops)
    (Con _ _, Var k _) -> (((Var (k++"t") 0:Var (k++"h") 0:ps), subst k (Con (Var (k++"h") 0) (Var (k++"t") 0)) rhs) : picks , ((p:ps),rhs) : drops)
    (One    , One    ) -> ((ps, rhs) : picks , drops)
    (One    , Var k _) -> ((ps, subst k One rhs) : picks , ((p:ps),rhs) : drops)
    (Tup _ _, Tup a b) -> (((a:b:ps), rhs) : picks , drops)
    (Tup _ _, Var k _) -> (((Var (k++"y") 0:Var (k++"x") 0:ps), subst k (Tup (Var (k++"x") 0) (Var (k++"y") 0)) rhs) : picks , ((p:ps),rhs) : drops)
    (Sym s  , Sym s' )
             | s == s' -> ((ps, rhs) : picks , drops)
    (Sym s  , Var k _) -> ((ps, subst k (Sym s) rhs) : picks , ((p:ps),rhs) : drops)
    (Rfl    , Rfl    ) -> ((ps, rhs) : picks , drops)
    (Rfl    , Var k _) -> ((ps, subst k Rfl rhs) : picks , ((p:ps),rhs) : drops)
    (Var _ _, p      ) -> unsupported
    (k      , App f x) -> callPatternSugar d book k f x p ps rhs cs
    x                  -> (picks , ((p:ps),rhs) : drops)
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
unpat d (Let v f)       = Let (unpat d v) (unpat d f)
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
unpat d (Lam n f)       = Lam n (\x -> unpat (d+1) (f x))
unpat d (App f x)       = App (unpat d f) (unpat d x)
unpat d (Eql t a b)     = Eql (unpat d t) (unpat d a) (unpat d b)
unpat d Rfl             = Rfl
unpat d (EqlM x f)      = EqlM (unpat d x) (unpat d f)
unpat d (Met i t x)     = Met i (unpat d t) (map (unpat d) x)
unpat d (Ind t)         = Ind (unpat d t)
unpat d (Frz t)         = Frz (unpat d t)
unpat d Era             = Era
unpat d (Sup l a b)     = Sup l (unpat d a) (unpat d b)
unpat d (Num t)         = Num t
unpat d (Val v)         = Val v
unpat d (Op2 o a b)     = Op2 o (unpat d a) (unpat d b)
unpat d (Op1 o a)       = Op1 o (unpat d a)
unpat d (Pri p)         = Pri p
unpat d (Loc s t)       = Loc s (unpat d t)
unpat d (Rwt a b f)     = Rwt (unpat d a) (unpat d b) (unpat d f)
unpat d (Pat [s] ms cs) = desugarWiths ms (match d s ms cs)
unpat d (Pat ss  ms []) = One
unpat d (Pat ss  ms cs) = error "unpat: multiple scrutinees after flattening"

-- Desugars `with` statements into `let` bindings.
desugarWiths :: [Move] -> Term -> Term
desugarWiths []           term = term
desugarWiths ((k,v) : ms) term = Let v (Lam k (\_ -> desugarWiths ms term))

match :: Int -> Term -> [Move] -> [Case] -> Term

-- match x { 0n: z ; 1n+p: s }
-- ---------------------------
-- ~x { 0n: z ; 1n+: λp. s }
match d x ms (([(cut -> Zer)], z) : ([(cut -> Suc p)], s) : _) =
  wrap d ms $ NatM x if_zer if_suc
  where if_zer = unpat d z
        if_suc = Lam (patOf d p) $ \x -> unpat (d+1) s

-- match x { 1n+p: s ; 0n: z }
-- ---------------------------
-- ~x { 0n: z ; 1n+: λp. s }
match d x ms (([(cut -> Suc p)], s) : ([(cut -> Zer)], z) : _) =
  wrap d ms $ NatM x if_zer if_suc
  where if_zer = unpat d z
        if_suc = Lam (patOf d p) $ \x -> unpat (d+1) s

-- match x { 0n: z ; k: v }
-- --------------------------------------
-- ~x { 0n: z ; 1n+: λk. v[k := 1n+k] }
match d x ms (([(cut -> Zer)], z) : ([(cut -> Var k i)], v) : _) =
  wrap d ms $ NatM x if_zer if_suc
  where if_zer = unpat d z
        if_suc = Lam k $ \x -> unpat (d+1) (subst k (Suc (Var k 0)) v)

-- match x { 1n+p: s ; k: v }
-- ------------------------------------
-- ~x { 0n: v[k := 0n] ; 1n+: λp. s }
match d x ms (([(cut -> Suc p)], s) : ([(cut -> Var k i)], v) : _) =
  wrap d ms $ NatM x if_zer if_suc
  where if_zer = unpat d (subst k Zer v)
        if_suc = Lam (patOf d p) $ \x -> unpat (d+1) s

-- match x { False: f ; True: t }
-- ------------------------------
-- ~x { False: f ; True: t }
match d x ms (([(cut -> Bt0)], f) : ([(cut -> Bt1)], t) : _) =
  wrap d ms $ BitM x (unpat d f) (unpat d t)

-- match x { True: t ; False: f }
-- ------------------------------
-- ~x { False: f ; True: t }
match d x ms (([(cut -> Bt1)], t) : ([(cut -> Bt0)], f) : _) =
  wrap d ms $ BitM x (unpat d f) (unpat d t)

-- match x { False: f ; k: v }
-- --------------------------------------
-- ~x { False: f ; True: v[k := True] }
match d x ms (([(cut -> Bt0)], f) : ([(cut -> Var k i)], v) : _) =
  wrap d ms $ BitM x (unpat d f) (unpat d (subst k Bt1 v))

-- match x { True: t ; k: v }
-- ---------------------------------------
-- ~x { False: v[k := False] ; True: t }
match d x ms (([(cut -> Bt1)], t) : ([(cut -> Var k i)], v) : _) =
  wrap d ms $ BitM x (unpat d (subst k Bt0 v)) (unpat d t)

-- match x { []: n ; h<>t: c }
-- ------------------------------
-- ~x { []: n ; <>: λh. λt. c }
match d x ms (([(cut -> Nil)], n) : ([(cut -> Con h t)], c) : _) =
  wrap d ms $ LstM x if_nil if_con
  where if_nil = unpat d n
        if_con = Lam (patOf d h) $ \_ -> Lam (patOf (d+1) t) $ \_ -> unpat (d+2) c

-- match x { h<>t: c ; []: n }
-- ------------------------------
-- ~x { []: n ; <>: λh. λt. c }
match d x ms (([(cut -> Con h t)], c) : ([(cut -> Nil)], n) : _) =
  wrap d ms $ LstM x if_nil if_con
  where if_nil = unpat d n
        if_con = Lam (patOf d h) $ \_ -> Lam (patOf (d+1) t) $ \_ -> unpat (d+2) c

-- match x { []: n ; k: v }
-- -----------------------------------------
-- ~x { []: n ; <>: λh. λt. v[k := h<>t] }
match d x ms (([(cut -> Nil)], n) : ([(cut -> Var k i)], v) : _) =
  wrap d ms $ LstM x if_nil if_con
  where if_nil = unpat d n
        if_con = Lam (nam d) $ \_ -> Lam (nam (d+1)) $ \_ -> unpat (d+2) (subst k (Con (var d) (var (d+1))) v)

-- match x { h<>t: c ; k: v }
-- ---------------------------------------
-- ~x { []: v[k := []] ; <>: λh. λt. c }
match d x ms (([(cut -> Con h t)], c) : ([(cut -> Var k i)], v) : _) =
  wrap d ms $ LstM x if_nil if_con
  where if_nil = unpat d (subst k Nil v)
        if_con = Lam (patOf d h) $ \_ -> Lam (patOf (d+1) t) $ \_ -> unpat (d+2) c

-- match x { (): u }
-- -----------------
-- ~x { (): u }
match d x ms cs@(([(cut -> One)], u) : _) =
  wrap d ms $ UniM x (unpat d u)

-- match x { (a,b): p }
-- --------------------
-- ~x { (,): λa. λb. p }
match d x ms (([(cut -> Tup a b)], p) : _) =
  wrap d ms $ SigM x if_tup
  where if_tup = Lam (patOf d a) $ \_ -> Lam (patOf (d+1) b) $ \_ -> unpat (d+2) p

-- match x { @S1: b1 ; @S2: b2 ; ... ; k: d }
-- ------------------------------------------
-- ~x { @S1:b1 ; @S2:b2 ; ... ; d }
match d x ms cs@(([(cut -> Sym _)], _) : _) =
  let (cBranches, defBranch) = collect cs
  in wrap d ms $ EnuM x cBranches defBranch
  where
    collect :: [Case] -> ([(String, Term)], Term)
    collect [] = ([], Lam "_" $ \_ -> One)
    collect (([(cut -> Sym s)], rhs) : rest) =
      let (cs, def) = collect rest
      in ((s, unpat d rhs) : cs, def)
    collect (([(cut -> Var k _)], rhs) : _) =
      ([], Lam k $ \_ -> unpat (d+1) rhs)
    collect (c:_) = error $ "match:invalid-Sym-case:" ++ show c

-- match x { {==}: r }
-- --------------------
-- ~x { {==}: r }
match d x ms (([(cut -> Rfl)], r) : _) =
  wrap d ms $ EqlM x (unpat d r)

-- match x { k: body }
-- -------------------
-- body[k := x]
match d x ms (([(cut -> Var k i)], body) : _) =
  unpat d (shove d ((k, x) : ms) body)

-- match x { }
-- -----------
-- λ{}
match d x ms [] =
  wrap d ms (EmpM x)

-- Invalid pattern
match d s ms cs = error $ "match - invalid pattern: " ++ show (d, s, ms, cs)

-- FIXME: wrap is untested; flattening 'with' clauses may not work properly

-- Completes a pattern-match using expression-based matches
-- Injects moved vars inwards using extra lams/apps
wrap :: Int -> [Move] -> Term -> Term
wrap d [] term = term
wrap d ms term = apps d (map snd ms) (lamsTerm d (map fst ms) term)

lamsTerm :: Int -> [Name] -> Term -> Term
lamsTerm d ks (NatM x z s) = NatM x (lams d ks z) (lams d ks s)
lamsTerm d ks (BitM x f t) = BitM x (lams d ks f) (lams d ks t)
lamsTerm d ks (LstM x n c) = LstM x (lams d ks n) (lams d ks c)
lamsTerm d ks (UniM x u)   = UniM x (lams d ks u)
lamsTerm d ks (SigM x p)   = SigM x (lams d ks p)
lamsTerm d ks (EnuM x c e) = EnuM x [(s, lams d ks t) | (s,t) <- c] (lams d ks e)
lamsTerm d ks (EqlM x r)   = EqlM x (lams d ks r)
lamsTerm d ks (EmpM x)     = EmpM x
lamsTerm d ks other        = error $ "lamsTerm: unexpected term: " ++ show other

-- Helpers
-- -------

-- Injects lambdas after skipping n lambdas
lams :: Int -> [Name] -> Term -> Term
lams d (k:ks) t = Lam k $ \_ -> lams (d+1) ks t
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
ctrOf d Zer       = (Zer , [])
ctrOf d (Suc p)   = (Suc (pat d p), [pat d p])
ctrOf d Bt0       = (Bt0 , [])
ctrOf d Bt1       = (Bt1 , [])
ctrOf d Nil       = (Nil , [])
ctrOf d (Con h t) = (Con (pat d h) (pat (d+1) t), [pat d h, pat (d+1) t])
ctrOf d One       = (One , [])
ctrOf d (Tup a b) = (Tup (pat d a) (pat (d+1) b), [pat d a, pat (d+1) b])
ctrOf d (Sym s)   = (Sym s, [])
ctrOf d Rfl       = (Rfl , [])
ctrOf d x         = (var d , [var d])

-- Subst a var for a value in a term
subst :: Name -> Term -> Term -> Term
subst name val term = go name val term where
  go name val term = case term of
    Var k _    -> if k == name then val else term
    Ref k      -> Ref k
    Sub t      -> Sub (go name val t)
    Fix k f    -> Fix k (\x -> go name val (f x))
    Let v f    -> Let (go name val v) (go name val f)
    Chk x t    -> Chk (go name val x) (go name val t)
    Set        -> Set
    Emp        -> Emp
    EmpM x     -> EmpM (go name val x)
    Uni        -> Uni
    One        -> One
    UniM x f   -> UniM (go name val x) (go name val f)
    Bit        -> Bit
    Bt0        -> Bt0
    Bt1        -> Bt1
    BitM x f t -> BitM (go name val x) (go name val f) (go name val t)
    Nat        -> Nat
    Zer        -> Zer
    Suc n      -> Suc (go name val n)
    NatM x z s -> NatM (go name val x) (go name val z) (go name val s)
    Lst t      -> Lst (go name val t)
    Nil        -> Nil
    Con h t    -> Con (go name val h) (go name val t)
    LstM x n c -> LstM (go name val x) (go name val n) (go name val c)
    Enu s      -> Enu s
    Sym s      -> Sym s
    EnuM x c e -> EnuM (go name val x) [(s, go name val t) | (s, t) <- c] (go name val e)
    Sig a b    -> Sig (go name val a) (go name val b)
    Tup a b    -> Tup (go name val a) (go name val b)
    SigM x f   -> SigM (go name val x) (go name val f)
    All a b    -> All (go name val a) (go name val b)
    Lam k f    -> Lam k (\x -> go name val (f x))
    App f x    -> App (go name val f) (go name val x)
    Eql t a b  -> Eql (go name val t) (go name val a) (go name val b)
    Rfl        -> Rfl
    EqlM x f   -> EqlM (go name val x) (go name val f)
    Met i t x  -> Met i (go name val t) (map (go name val) x)
    Ind t      -> Ind (go name val t)
    Frz t      -> Frz (go name val t)
    Era        -> Era
    Sup l a b  -> Sup l (go name val a) (go name val b)
    Num t      -> Num t
    Val v      -> Val v
    Op2 o a b  -> Op2 o (go name val a) (go name val b)
    Op1 o a    -> Op1 o (go name val a)
    Pri p      -> Pri p
    Loc s t    -> Loc s (go name val t)
    Rwt a b x  -> Rwt (go name val a) (go name val b) (go name val x)
    Pat s m c  -> Pat (map (go name val) s) m (map cse c)
      where cse (pats, rhs) = (map (go name val) pats, go name val rhs)

unsupported :: a
unsupported = unsafePerformIO $ do
  putStrLn $ "Unsupported pattern-match shape."
  putStrLn $ "Support for it will be added in a future update."
  exitFailure
