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

module Core.Adjust.FlattenPats where

import Data.List (nub, find)
import System.Exit
import System.IO
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

import Core.Bind
import Core.Show
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

flattenPats :: Int -> Span -> Book -> Term -> Term
flattenPats d span book (Loc sp t) = (Loc sp (flattenPats d sp book t))
flattenPats d span book term       = case term of
  (Var n i)     -> Var n i
  (Ref n i)     -> Ref n  i
  (Sub t)       -> Sub (flattenPats d span book t)
  (Fix n f)     -> Fix n (\x -> flattenPats (d+1) span book (f x))
  (Let k t v f) -> Let k (fmap (flattenPats d span book) t) (flattenPats d span book v) (\x -> flattenPats (d+1) span book (f x))
  (Use k v f)   -> Use k (flattenPats d span book v) (\x -> flattenPats (d+1) span book (f x))
  Set           -> Set
  (Chk x t)     -> Chk (flattenPats d span book x) (flattenPats d span book t)
  (Tst x)       -> Tst (flattenPats d span book x)
  Emp           -> Emp
  EmpM          -> EmpM
  Uni           -> Uni
  One           -> One
  (UniM f)      -> UniM (flattenPats d span book f)
  Bit           -> Bit
  Bt0           -> Bt0
  Bt1           -> Bt1
  (BitM f t)    -> BitM (flattenPats d span book f) (flattenPats d span book t)
  Nat           -> Nat
  Zer           -> Zer
  (Suc n)       -> Suc (flattenPats d span book n)
  (NatM z s)    -> NatM (flattenPats d span book z) (flattenPats d span book s)
  (Lst t)       -> Lst (flattenPats d span book t)
  Nil           -> Nil
  (Con h t)     -> Con (flattenPats d span book h) (flattenPats d span book t)
  (LstM n c)    -> LstM (flattenPats d span book n) (flattenPats d span book c)
  (Enu s)       -> Enu s
  (Sym s)       -> Sym s
  (EnuM c e)    -> EnuM [(s, flattenPats d span book t) | (s, t) <- c] (flattenPats d span book e)
  (Sig a b)     -> Sig (flattenPats d span book a) (flattenPats d span book b)
  (Tup a b)     -> Tup (flattenPats d span book a) (flattenPats d span book b)
  (SigM f)      -> SigM (flattenPats d span book f)
  (All a b)     -> All (flattenPats d span book a) (flattenPats d span book b)
  (Lam n t f)   -> Lam n (fmap (flattenPats d span book) t) (\x -> flattenPats (d+1) span book (f x))
  (App f x)     -> App (flattenPats d span book f) (flattenPats d span book x)
  (Eql t a b)   -> Eql (flattenPats d span book t) (flattenPats d span book a) (flattenPats d span book b)
  Rfl           -> Rfl
  (EqlM f)      -> EqlM (flattenPats d span book f)
  (Met i t x)   -> Met i (flattenPats d span book t) (map (flattenPats d span book) x)
  Era           -> Era
  (Sup l a b)   -> Sup (flattenPats d span book l) (flattenPats d span book a) (flattenPats d span book b)
  (SupM l f)    -> SupM (flattenPats d span book l) (flattenPats d span book f)
  (Frk l a b)   -> Frk (flattenPats d span book l) (flattenPats d span book a) (flattenPats d span book b)
  (Rwt e f)     -> Rwt (flattenPats d span book e) (flattenPats d span book f)
  (Num t)       -> Num t
  (Val v)       -> Val v
  (Op2 o a b)   -> Op2 o (flattenPats d span book a) (flattenPats d span book b)
  (Op1 o a)     -> Op1 o (flattenPats d span book a)
  (Pri p)       -> Pri p
  (Log s x)     -> Log (flattenPats d span book s) (flattenPats d span book x)
  -- (Loc s t)     -> Loc s (flattenPats d span book t)
  (Pat s m c)   -> simplify d $ flattenPat d span book (Pat s m c)

isVarCol :: [Case] -> Bool
isVarCol []                        = True
isVarCol (((cut->Var _ _):_,_):cs) = isVarCol cs
isVarCol _                         = False

flattenPat :: Int -> Span -> Book -> Term -> Term
flattenPat d span book pat =
  -- trace ("FLATTEN: " ++ show pat) $
  flattenPatGo d book pat where
    flattenPatGo d book pat@(Pat (s:ss) ms css@((((cut->Var k i):ps),rhs):cs)) | isVarCol css =
      -- trace (">> var: " ++ show pat) $
      flattenPats d span book $ Pat ss ms (joinVarCol (d+1) span book s (((Var k i:ps),rhs):cs))
      -- flattenPats d span book $ Pat ss (ms++[(k,s)]) (joinVarCol (d+1) (Var k 0) (((Var k i:ps),rhs):cs))
    flattenPatGo d book pat@(Pat (s:ss) ms cs@(((pp:ps0),rhs0):cs0)) =
      -- trace (">> ctr: " ++ show p ++ " " ++ show pat
          -- ++ "\n>> - picks: " ++ show picks
          -- ++ "\n>> - drops: " ++ show drops) $
      Pat [s] moves [([ct], flattenPats (d+length fs) span book picks), ([var d], flattenPats (d+1) span book drops)] where
        p        = cut pp
        (ct0,fs) = ctrOf d p
        -- Preserve location if the pattern was a located unit '()' or tuple
        ct       = case (ct0, pp) of
                     (One, Loc sp (cut -> One)) -> Loc sp One
                     (Tup a b, Loc sp (cut -> Tup _ _)) -> Loc sp (Tup a b)
                     _                           -> ct0
        (ps,ds)  = peelCtrCol d span book ct cs
        moves    = ms
        -- moves   = ms ++ map (\ (s,i) -> (patOf (d+i) s, s)) (zip ss [0..])
        picks   = Pat (fs   ++ ss) ms ps
        drops   = Pat (var d : ss) ms ds
    flattenPatGo d book pat@(Pat [] ms (([],rhs):cs)) =
      flattenPats d span book rhs
    flattenPatGo d book (Loc l t) =
      Loc l (flattenPat d span book t)
    flattenPatGo d book pat =
      pat

-- Converts an all-variable column to a 'with' statement
-- match x y { case x0 @A: F(x0) ; case x1 @B: F(x1) }
-- --------------------------------------------------- joinVarCol k
-- match y { with k=x case @A: F(k) ; case @B: F(k) }
joinVarCol :: Int -> Span -> Book -> Term -> [Case] -> [Case]
joinVarCol d span book k ((((cut->Var j _):ps),rhs):cs) = (ps, bindVarByName j k rhs) : joinVarCol d span book k cs
joinVarCol d span book k ((((cut->ctr    ):ps),rhs):cs) = errorWithSpan span "Redundant pattern."
joinVarCol d span book k cs                             = cs

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
peelCtrCol :: Int -> Span -> Book -> Term -> [Case] -> ([Case],[Case])
peelCtrCol d span book (cut->k) ((((cut->p):ps),rhs):cs) = 
  -- trace (">> peel " ++ show k ++ " ~ " ++ show p) $
  case (k,p) of
    (Zer      , Zer    )   -> ((ps, rhs) : picks , drops)
    (Zer      , Var k _)   -> ((ps, bindVarByName k Zer rhs) : picks , ((p:ps),rhs) : drops)
    (Suc _    , Suc x  )   -> (((x:ps), rhs) : picks , drops)
    (Suc _    , Var k _)   -> (((Var k 0:ps), bindVarByName k (Suc (Var k 0)) rhs) : picks , ((p:ps),rhs) : drops)
    (Bt0      , Bt0    )   -> ((ps, rhs) : picks , drops)
    (Bt0      , Var k _)   -> ((ps, bindVarByName k Bt0 rhs) : picks , ((p:ps),rhs) : drops)
    (Bt1      , Bt1    )   -> ((ps, rhs) : picks , drops)
    (Bt1      , Var k _)   -> ((ps, bindVarByName k Bt1 rhs) : picks , ((p:ps),rhs) : drops)
    (Nil      , Nil    )   -> ((ps, rhs) : picks , drops)
    (Nil      , Var k _)   -> ((ps, bindVarByName k Nil rhs) : picks , ((p:ps),rhs) : drops)
    (Con _ _  , Con h t)   -> (((h:t:ps), rhs) : picks , drops)
    (Con _ _  , Var k _)   -> (((Var (k++"h") 0:Var (k++"t") 0:ps), bindVarByName k (Con (Var (k++"h") 0) (Var (k++"t") 0)) rhs) : picks , ((p:ps),rhs) : drops)
    (Loc sp One, One    )   -> ((ps, rhs) : picks , drops)
    (One      , One    )   -> ((ps, rhs) : picks , drops)
    (Loc sp One, Var k _)   -> ((ps, bindVarByName k One rhs) : picks , ((p:ps),rhs) : drops)
    (One      , Var k _)   -> ((ps, bindVarByName k One rhs) : picks , ((p:ps),rhs) : drops)
    (Loc sp (Tup _ _), Tup a b) -> (((a:b:ps), rhs) : picks , drops)
    (Tup _ _  , Tup a b)   -> (((a:b:ps), rhs) : picks , drops)
    (Loc sp (Tup _ _), Var k _) -> (((Var (k++"x") 0:Var (k++"y") 0:ps), bindVarByName k (Tup (Var (k++"x") 0) (Var (k++"y") 0)) rhs) : picks , ((p:ps),rhs) : drops)
    (Tup _ _  , Var k _)   -> (((Var (k++"x") 0:Var (k++"y") 0:ps), bindVarByName k (Tup (Var (k++"x") 0) (Var (k++"y") 0)) rhs) : picks , ((p:ps),rhs) : drops)
    (Sym s    , Sym s' )
               | s == s'   -> ((ps, rhs) : picks , drops)
    (Sym s    , Var k _)   -> ((ps, bindVarByName k (Sym s) rhs) : picks , ((p:ps),rhs) : drops)
    (Sup l _ _, Sup r a b) -> (((a:b:ps), rhs) : picks , drops)
    (Sup l _ _, Var k _)   -> (((Var (k++"a") 0:Var (k++"b") 0:ps), bindVarByName k (Sup l (Var (k++"a") 0) (Var (k++"b") 0)) rhs) : picks , ((p:ps),rhs) : drops)
    (Rfl      , Rfl    )   -> ((ps, rhs) : picks , drops)
    (Rfl      , Var k _)   -> ((ps, bindVarByName k Rfl rhs) : picks , ((p:ps),rhs) : drops)
    (Var _ _  , p      )   -> errorWithSpan span "Unsupported pattern-match shape.\nSupport for it will be added in a future update."
    (k        , App f x)   -> callPatternSugar d span book k f x p ps rhs cs
    x                      -> (picks , ((p:ps),rhs) : drops)
  where (picks, drops) = peelCtrCol d span book k cs
peelCtrCol d span book k cs = (cs,cs)

-- Allows using a function call in a pattern. Example:
--   case Foo(p): return 1n + add(p,b)
--   (where 'Foo' is a user-defined function)
callPatternSugar :: Int -> Span -> Book -> Term -> Term -> Term -> Term -> [Term] -> Term -> [Case] -> ([Case],[Case])
callPatternSugar d span book k f x p ps rhs cs =
  peelCtrCol d span book k (((exp:ps),rhs):cs)
  where (fn,xs) = collectApps (App f x)  []
        exp     = normal book $ foldl App ref xs
        ref     = case fn of
          Ref k i   -> Ref k i
          Var k _   -> Ref k 1
          otherwise -> errorWithSpan span ("Invalid call pattern: " ++ show (App f x))

-- Simplify
-- ========
-- Removes redundant matches, adjusts form

-- >> match _x7 M{ case (False): () case (_x8): match _x8 M{ } }

-- Substitutes a move list into an expression
shove :: Int -> [Move] -> Term -> Term
shove d ms term = foldr (\ (k,v) x -> bindVarByName k v x) term ms 

simplify :: Int -> Term -> Term
simplify d (Pat ss ms cs) =
  case Pat ss ms (map (\ (p, c) -> (p, simplify d c)) cs) of
    pat@(Pat [] ms (([],rhs):cs)) ->
      -- simplify d (shove d ms rhs)
      simplify d rhs
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
                -- where csA = map (\ (p, rhs) -> (p, shove d ms rhs)) cs'
                where csA = map (\ (p, rhs) -> (p, rhs)) cs'
                      csB = merge d cs
merge d ((p,rhs):cs) = (p, rhs) : merge d cs
merge d []           = []

-- match { with x=A ... case: F(x,...) ... }
-- ----------------------------------------- simplify-decay
-- F(A,...)
decay :: Int -> Term -> Term
-- decay d (Pat [] ms (([],rhs):cs)) = simplify d (shove d ms rhs)
decay d (Pat [] ms (([],rhs):cs)) = simplify d rhs
decay d pat                       = pat

-- Helpers
-- -------

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
ctrOf d (Sup l a b) = (Sup l (pat d a) (pat (d+1) b), [pat d a, pat (d+1) b])
ctrOf d Rfl         = (Rfl , [])
ctrOf d x           = (var d , [var d])
