{-./../Type.hs-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}

module Core.Adjust.FlattenPats where

-- -- Pattern Matching Flattener
-- -- ==========================
-- -- 
-- -- This algorithm converts pattern matching expressions with multiple 
-- -- scrutinees into nested case trees with single scrutinees. Example:
-- --
-- -- match x y
-- -- | 0n     0n          = X0
-- -- | (1n+x) 0n          = X1
-- -- | 0n     (1n+y)      = X2
-- -- | (1n+x) (1n+0n)     = X3
-- -- | (1n+x) (1n+(1n+z)) = X4
-- -- ------------------------- flatten
-- -- match x:
-- --   case 0n:
-- --     match y:
-- --       case 0n: X0
-- --       case 1+y: X2
-- --   case 1n+x:
-- --     match y:
-- --       case 0n: X1
-- --       case 1n+y_:
-- --         match y_:
-- --           case 0n: X3
-- --           case 1n+z: X4

import Data.List (nub, find)
import System.Exit
import System.IO
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

import Core.Bind
import Core.FreeVars
import Core.Show
import Core.Type
import Core.WHNF
import Core.Equal

-- Flattener
-- =========
-- Converts pattern-matches into if-lets, forcing the shape:
--   match x { with ... ; case C{}: ... ; case x: ... }
-- After this transformation, the match will have exactly:
-- - 1 scrutinee
-- - 1 value case
-- - 1 default case
-- Outer scrutinees will be moved inside via 'with'.

flattenPats :: Int -> Span -> Book -> Term -> Term
flattenPats d span book term = go d span term where
  go d sp (Var n i)     = Var n i
  go d sp (Ref n i)     = Ref n i
  go d sp (Sub t)       = Sub (go d sp t)
  go d sp (Fix n f)     = Fix n (\x -> go (d+1) sp (f x))
  go d sp (Let k t v f) = Let k (fmap (go d sp) t) (go d sp v) (\x -> go (d+1) sp (f x))
  go d sp (Use k v f)   = Use k (go d sp v) (\x -> go (d+1) sp (f x))
  go d sp Set           = Set
  go d sp (Chk x t)     = Chk (go d sp x) (go d sp t)
  go d sp Emp           = Emp
  go d sp EmpM          = EmpM
  go d sp Uni           = Uni
  go d sp One           = One
  go d sp (UniM f)      = UniM (go d sp f)
  go d sp Bit           = Bit
  go d sp Bt0           = Bt0
  go d sp Bt1           = Bt1
  go d sp (BitM f t)    = BitM (go d sp f) (go d sp t)
  go d sp Nat           = Nat
  go d sp Zer           = Zer
  go d sp (Suc n)       = Suc (go d sp n)
  go d sp (NatM z s)    = NatM (go d sp z) (go d sp s)
  go d sp (Lst t)       = Lst (go d sp t)
  go d sp Nil           = Nil
  go d sp (Con h t)     = Con (go d sp h) (go d sp t)
  go d sp (LstM n c)    = LstM (go d sp n) (go d sp c)
  go d sp (ADT n ts)    = ADT n (map (go d sp) ts)
  go d sp (Ctr n ts)    = Ctr n (map (go d sp) ts)
  go d sp (ADTM n cs u) = ADTM n [(c, go d sp t) | (c, t) <- cs] (fmap (go d sp) u)
  go d sp (Sig a b)     = Sig (go d sp a) (go d sp b)
  go d sp (Tup a b)     = Tup (go d sp a) (go d sp b)
  go d sp (SigM f)      = SigM (go d sp f)
  go d sp (All a b)     = All (go d sp a) (go d sp b)
  go d sp (Lam n t f)   = Lam n (fmap (go d sp) t) (\x -> go (d+1) sp (f x))
  go d sp (App f x)     = App (go d sp f) (go d sp x)
  go d sp (Eql t a b)   = Eql (go d sp t) (go d sp a) (go d sp b)
  go d sp Rfl           = Rfl
  go d sp (EqlM f)      = EqlM (go d sp f)
  go d sp (Met i t x)   = Met i (go d sp t) (map (go d sp) x)
  go d sp Era           = Era
  go d sp (Sup l a b)   = Sup (go d sp l) (go d sp a) (go d sp b)
  go d sp (SupM l f)    = SupM (go d sp l) (go d sp f)
  go d sp (Frk l a b)   = Frk (go d sp l) (go d sp a) (go d sp b)
  go d sp (Rwt e f)     = Rwt (go d sp e) (go d sp f)
  go d sp (Num t)       = Num t
  go d sp (Val v)       = Val v
  go d sp (Op2 o a b)   = Op2 o (go d sp a) (go d sp b)
  go d sp (Op1 o a)     = Op1 o (go d sp a)
  go d sp (Pri p)       = Pri p
  go d _  (Loc sp t)    = Loc sp (go d sp t)
  go d sp (Log s x)     = Log (go d sp s) (go d sp x)
  go d sp (Pat s m c)   = simplify d $ go d sp (Pat s m c)

isVarCol :: [Case] -> Bool
isVarCol []                        = True
isVarCol (((cut->Var _ _):_,_):cs) = isVarCol cs
isVarCol _                         = False

-- Count fields in a pattern
countPatternFields :: Term -> Int
countPatternFields One       = 0
countPatternFields (Tup a b) = 1 + countPatternFields b
countPatternFields _         = 1

flattenPat :: Int -> Span -> Book -> Term -> Term
flattenPat d span book pat =
  -- trace ("FLATTEN: " ++ show pat) $
  flattenPatGo d book pat where
    flattenPatGo d book pat@(Pat (s:ss) ms css@((((cut->Var k i):ps),rhs):cs)) | isVarCol css =
      -- trace (">> var: " ++ show pat) $
      flattenPats d span book $ Pat ss ms (joinVarCol (d+1) span book s (((Var k i:ps),rhs):cs))
      -- flattenPats d span book $ Pat ss (ms++[(k,s)]) (joinVarCol (d+1) (Var k 0) (((Var k i:ps),rhs):cs))
    flattenPatGo d book pat@(Pat (s:ss) ms cs@((((cut->p):_),_):_)) =
      -- trace (">> ctr: " ++ show p ++ " " ++ show pat
          -- ++ "\n>> - picks: " ++ show picks
          -- ++ "\n>> - drops: " ++ show drops) $
      Pat [s] moves [([ct], flattenPats (d+length fs) span book picks), ([var d], flattenPats (d+1) span book drops)] where
        (ct,fs) = ctrOf d p
        (ps,ds) = peelCtrCol d span book ct cs
        moves   = ms
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
-- match x y { case x0 C{}: F(x0) ; case x1 D{}: F(x1) }
-- --------------------------------------------------- joinVarCol k
-- match y { with k=x case C{}: F(k) ; case D{}: F(k) }
joinVarCol :: Int -> Span -> Book -> Term -> [Case] -> [Case]
joinVarCol d span book k ((((cut->Var j _):ps),rhs):cs) = (ps, bindVarByName j k rhs) : joinVarCol d span book k cs
joinVarCol d span book k ((((cut->ctr    ):ps),rhs):cs) = errorWithSpan span "Redundant pattern."
joinVarCol d span book k cs                             = cs

-- Peels a constructor layer from a column
-- match x y:
--   case 0n      C{}: A
--   case (1n+p)  D{}: B(p)
--   case (1n+p)  E{}: C(p)
-- ------------------------- peel 0n , peel (1n+k)
-- match x:
--   with y
--   case 0n: # ↓ peel 0n
--     match y:
--       case C{}: A
--   case 1n+k: # ↓ peel (1n+k)
--     match k y:
--       case p D{}: B(p)
--       case p E{}: C(p)
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
    (One      , One    )   -> ((ps, rhs) : picks , drops)
    (One      , Var k _)   -> ((ps, bindVarByName k One rhs) : picks , ((p:ps),rhs) : drops)
    (Tup _ _  , Tup a b)   -> (((a:b:ps), rhs) : picks , drops)
    (Tup _ _  , Var k _)   -> (((Var (k++"x") 0:Var (k++"y") 0:ps), bindVarByName k (Tup (Var (k++"x") 0) (Var (k++"y") 0)) rhs) : picks , ((p:ps),rhs) : drops)
    (Ctr n _  , Ctr n' xs)
               | n == n'   -> ((xs++ps, rhs) : picks , drops)
    (Ctr n _  , Var k _)   -> let vars = [Var (k++"_"++show i) 0 | i <- [0..length(getCtrFields book n)-1]]
                              in ((vars++ps, bindVarByName k (Ctr n vars) rhs) : picks , ((p:ps),rhs) : drops)
    (Sup l _ _, Sup r a b) -> (((a:b:ps), rhs) : picks , drops)
    (Sup l _ _, Var k _)   -> (((Var (k++"a") 0:Var (k++"b") 0:ps), bindVarByName k (Sup l (Var (k++"a") 0) (Var (k++"b") 0)) rhs) : picks , ((p:ps),rhs) : drops)
    (Rfl      , Rfl    )   -> ((ps, rhs) : picks , drops)
    (Rfl      , Var k _)   -> ((ps, bindVarByName k Rfl rhs) : picks , ((p:ps),rhs) : drops)
    (Var _ _  , p      )   -> errorWithSpan span "Unsupported pattern-match shape.\nSupport for it will be added in a future update."
    (k        , App f x)   -> callPatternSugar d span book k f x p ps rhs cs
    x                      -> (picks , ((p:ps),rhs) : drops)
  where (picks, drops) = peelCtrCol d span book k cs
peelCtrCol d span book k cs = (cs,cs)

-- Helper to get constructor field count
getCtrFields :: Book -> Name -> [()]
getCtrFields book ctrName = 
  case getCtr book ctrName of
    Just (_, ctrType) -> getCtrFieldsFromType (stripParams ctrType)
    Nothing -> []
  where
    -- Strip parameter lambdas until we reach the motive lambda
    stripParams :: Type -> Type
    stripParams (Lam _ _ f) = stripParams (f (Var "_" 0))
    stripParams t           = t
    
    getCtrFieldsFromType :: Type -> [()]
    getCtrFieldsFromType (All _ (Lam _ _ f)) = () : getCtrFieldsFromType (f (Var "_" 0))
    getCtrFieldsFromType _                   = []

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

-- Substitutes a move list into an expression
shove :: Int -> [Move] -> Term -> Term
shove d ms term = foldr (\ (k,v) x -> bindVarByName k v x) term ms 

simplify :: Int -> Term -> Term
simplify d (Pat ss ms cs) =
  case Pat ss ms (map (\ (p, c) -> (p, simplify d c)) cs) of
    pat@(Pat [] ms (([],rhs):cs)) -> simplify d (shove d ms rhs)
    pat@(Pat ss ms cs)            -> Pat ss ms (merge d cs)
simplify d (Loc l t) = Loc l (simplify d t)
simplify d pat       = pat

-- Merges redundant case-match chains into parent
-- ... case x: match x { case A{}: A ; case B{}: B ... } ...
-- --------------------------------------------------- simplify
-- ... case A{}: A ; case B{}: B ...
merge :: Int -> [Case] -> [Case]
merge d (([Var x _], (Pat [Var x' _] ms cs')) : cs)
  | x == x' = csA ++ csB
  where csA = map (\ (p, rhs) -> (p, shove d ms rhs)) cs'
        csB = merge d cs
merge d ((p,rhs):cs) = (p, rhs) : merge d cs
merge d [] = []

-- match { with x=A ... case: F(x,...) ... }
-- ----------------------------------------- simplify-decay
-- F(A,...)
decay :: Int -> Term -> Term
decay d (Pat [] ms (([],rhs):cs)) = simplify d (shove d ms rhs)
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
ctrOf d (Ctr n xs)  = (Ctr n pats, pats) where pats = [pat (d+i) x | (i,x) <- zip [0..] xs]
ctrOf d (Sup l a b) = (Sup l (pat d a) (pat (d+1) b), [pat d a, pat (d+1) b])
ctrOf d Rfl         = (Rfl , [])
ctrOf d x           = (var d , [var d])
