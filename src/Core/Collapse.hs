{-./Type.hs-}
{-./WHNF.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Collapse where

import Control.Monad (ap)
import qualified Data.IntMap.Strict as IM

import Debug.Trace

import Core.Type hiding (Bits(..))
import Core.WHNF (termToInt)

-- The Collapse Monad 
-- ------------------
-- A Collapse is a tree of superposed values
data Collapse a = CSup Int (Collapse a) (Collapse a) | CVal a | CEra
  deriving Show

-- This is a helper type for cbind, not exported.
data Bin = O Bin | I Bin | E

cbind :: Collapse a -> (a -> Collapse b) -> Collapse b
cbind k f = fork k IM.empty where
  -- fork :: Collapse a -> IntMap (Bin -> Bin) -> Collapse b
  fork CEra         paths = CEra
  fork (CVal v)     paths = pass (f v) (IM.map (\x -> x E) paths)
  fork (CSup k x y) paths =
    let lft = fork x $ IM.alter (\x -> Just (maybe (putO id) putO x)) k paths in
    let rgt = fork y $ IM.alter (\x -> Just (maybe (putI id) putI x)) k paths in
    CSup k lft rgt 
  -- pass :: Collapse b -> IntMap Bin -> Collapse b
  pass CEra         paths = CEra
  pass (CVal v)     paths = CVal v
  pass (CSup k x y) paths = case IM.lookup k paths of
    Just (O p) -> pass x (IM.insert k p paths)
    Just (I p) -> pass y (IM.insert k p paths)
    Just E     -> CSup k (pass x paths) (pass y paths)
    Nothing    -> CSup k (pass x paths) (pass y paths)
  -- putO :: (Bin -> Bin) -> (Bin -> Bin)
  putO bs = \x -> bs (O x)
  -- putI :: (Bin -> Bin) -> (Bin -> Bin) 
  putI bs = \x -> bs (I x)

instance Functor Collapse where
  fmap f (CVal v)     = CVal (f v)
  fmap f (CSup k x y) = CSup k (fmap f x) (fmap f y)
  fmap _ CEra         = CEra

instance Applicative Collapse where
  pure  = CVal
  (<*>) = ap

instance Monad Collapse where
  return = pure
  (>>=)  = cbind

-- Simple Queue
-- ------------
-- Allows pushing to an end, and popping from another.
data SQ a = SQ [a] [a]

sqPop :: SQ a -> Maybe (a, SQ a)
sqPop (SQ [] [])     = Nothing
sqPop (SQ [] ys)     = sqPop (SQ (reverse ys) [])
sqPop (SQ (x:xs) ys) = Just (x, SQ xs ys)

sqPut :: a -> SQ a -> SQ a
sqPut x (SQ xs ys) = SQ xs (x:ys)

-- Flattener
-- ---------

flatten :: Collapse a -> [a]
flatten term = go term (SQ [] [] :: SQ (Collapse a)) where
  go (CSup _ a b) sq = go CEra (sqPut b $ sqPut a $ sq)
  go (CVal x)     sq = x : go CEra sq
  go CEra         sq = case sqPop sq of
    Just (v,sq) -> go v sq
    Nothing     -> []

-- Collapser
-- ---------

collapse :: Int -> Book -> Term -> Collapse Term
collapse dep book term = case term of
  -- Variables
  Var k i -> return $ Var k i
  Ref k   -> return $ Ref k
  Sub t   -> do
    t' <- collapse dep book t
    return $ Sub t'

  -- Definitions
  Fix k f -> do
    f' <- collapse (dep+1) book (f (Var k dep))
    return $ Fix k (\_ -> f')
  Let v f -> do
    v' <- collapse dep book v
    f' <- collapse dep book f
    return $ Let v' f'

  -- Universe
  Set -> return Set

  -- Annotation
  Chk x t -> do
    x' <- collapse dep book x
    t' <- collapse dep book t
    return $ Chk x' t'

  -- Empty
  Emp     -> return Emp
  EmpM x  -> do
    x' <- collapse dep book x
    return $ EmpM x'

  -- Unit
  Uni       -> return Uni
  One       -> return One
  UniM x f  -> do
    x' <- collapse dep book x
    f' <- collapse dep book f
    return $ UniM x' f'

  -- Bool
  Bit         -> return Bit
  Bt0         -> return Bt0
  Bt1         -> return Bt1
  BitM x f t  -> do
    x' <- collapse dep book x
    f' <- collapse dep book f
    t' <- collapse dep book t
    return $ BitM x' f' t'

  -- Nat
  Nat         -> return Nat
  Zer         -> return Zer
  Suc n       -> do
    n' <- collapse dep book n
    return $ Suc n'
  NatM x z s  -> do
    x' <- collapse dep book x
    z' <- collapse dep book z
    s' <- collapse dep book s
    return $ NatM x' z' s'

  -- List
  Lst t       -> do
    t' <- collapse dep book t
    return $ Lst t'
  Nil         -> return Nil
  Con h t     -> do
    h' <- collapse dep book h
    t' <- collapse dep book t
    return $ Con h' t'
  LstM x n c  -> do
    x' <- collapse dep book x
    n' <- collapse dep book n
    c' <- collapse dep book c
    return $ LstM x' n' c'

  -- Enum
  Enu s       -> return $ Enu s
  Sym s       -> return $ Sym s
  EnuM x cs e -> do
    x' <- collapse dep book x
    cs' <- mapM (\(s,t) -> (,) s <$> collapse dep book t) cs
    e' <- collapse dep book e
    return $ EnuM x' cs' e'

  -- Numbers
  Num nt        -> return $ Num nt
  Val nv        -> return $ Val nv
  Op2 op a b    -> do
    a' <- collapse dep book a
    b' <- collapse dep book b
    return $ Op2 op a' b'
  Op1 op a      -> do
    a' <- collapse dep book a
    return $ Op1 op a'

  -- Pair
  Sig a b     -> do
    a' <- collapse dep book a
    b' <- collapse dep book b
    return $ Sig a' b'
  Tup a b     -> do
    a' <- collapse dep book a
    b' <- collapse dep book b
    return $ Tup a' b'
  SigM x f    -> do
    x' <- collapse dep book x
    f' <- collapse dep book f
    return $ SigM x' f'

  -- Function
  All a b     -> do
    a' <- collapse dep book a
    b' <- collapse dep book b
    return $ All a' b'
  Lam k f     -> do
    f' <- collapse (dep+1) book (f (Var k dep))
    return $ Lam k (\_ -> f')
  App f x     -> do
    f' <- collapse dep book f
    x' <- collapse dep book x
    return $ App f' x'

  -- Equality
  Eql t a b   -> do
    t' <- collapse dep book t
    a' <- collapse dep book a
    b' <- collapse dep book b
    return $ Eql t' a' b'
  Rfl         -> return Rfl
  EqlM x f    -> do
    x' <- collapse dep book x
    f' <- collapse dep book f
    return $ EqlM x' f'

  -- MetaVar
  Met k t c   -> do
    t' <- collapse dep book t
    c' <- mapM (collapse dep book) c
    return $ Met k t' c'

  -- Hints
  Ind t       -> do
    t' <- collapse dep book t
    return $ Ind t'
  Frz t       -> do
    t' <- collapse dep book t
    return $ Frz t'

  -- Superpositions
  Era -> CEra

  -- NOTE: this case is different from the others because `Sup` is a control
  -- operator for the Collapse Monad, not a common term. As such, we don't use
  -- the Monadic binder '<-' here, but rather, just create a CSup directly.
  Sup l a b ->
    collapse dep book l >>= \l_val ->
      case termToInt book l_val of
        Just k  -> CSup k (collapse dep book a) (collapse dep book b)
        Nothing -> CEra -- Invalid superposition label

  SupM x l f ->
    error "TODO"

  -- Errors
  Loc _ t     -> collapse dep book t
  Rwt a b x   -> do
    a' <- collapse dep book a
    b' <- collapse dep book b
    x' <- collapse dep book x
    return $ Rwt a' b' x'

  -- Logging
  Log s x -> do
    s' <- collapse dep book s
    x' <- collapse dep book x
    return $ Log s' x'

  -- Primitive
  Pri p       -> return $ Pri p

  -- Sugars
  Pat ts ms cs -> error "unreachable"
  Frk l a b    -> error "unreachable"

-- doCollapse
-- ----------

doCollapse :: Book -> Term -> [Term]
doCollapse book term = flatten (collapse 0 book term)
