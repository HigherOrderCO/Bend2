{-# LANGUAGE BlockArguments #-}

module Core.Termination where

import Debug.Trace (trace)
import Control.Monad.State (StateT, evalStateT, modify, get, lift)
import Control.Monad.Except
import Control.Monad (foldM, liftM2, when)
import qualified Data.Map as M
import Data.Maybe (isNothing)

import Core.Type
import Core.Flatten

data TerminationError
  = UnknownTermination Term
  | NonlinearVar Term
  | NonstructuralRecursion Term

data TerminationResult a
  = TerminationDone a
  | TerminationFail TerminationError

instance Functor TerminationResult where
  fmap f (TerminationDone a) = TerminationDone (f a)
  fmap _ (TerminationFail e) = TerminationFail e

instance Applicative TerminationResult where
  pure                                    = TerminationDone
  TerminationDone f <*> TerminationDone a = TerminationDone (f a)
  TerminationFail e <*> _                 = TerminationFail e
  _                 <*> TerminationFail e = TerminationFail e

instance Monad TerminationResult where
  TerminationDone a >>= f = f a
  TerminationFail e >>= _ = TerminationFail e

instance Show TerminationError where
  show (UnknownTermination term) = 
    "Unknown termination: " ++ show term
  show (NonlinearVar term) = 
    "Nonlinear Variable: " ++ show term
  show (NonstructuralRecursion term) = 
    "Non-structural recursion: " ++ show term

-- Check all definitions in a Book
terminatesBook :: Book -> TerminationResult ()
terminatesBook book@(Book defs) = (mapM_ terminatesDef (M.toList defs))
  where
    terminatesDef (name, (term, typ)) = terminates book term

terminates :: Book -> Term -> TerminationResult ()
terminates book@(Book defs) term = evalStateT (terminatesM book term) (foldl (\acc (name,term) -> M.insert name 0 acc) M.empty (M.toList defs))

type TermM = StateT (M.Map Name Int) TerminationResult

showFunc (Fix x f) = x ++ ":=" ++ showFunc(f (Var x 0))
showFunc t = show t

-- FIXME: doesn't detect mutual recursion, testStructural fails
terminatesM :: Book -> Term -> TermM () 
terminatesM book term = do
  st <- get
  -- let termRepr = case term of
  --       (Fix x f) -> x ++ ":= " ++ show()
  --       _ -> "BB"
  let msg = trace (showFunc term ++ " with " ++ show st) ()
  msg `seq` pure ()
  case term of
    -- -- Variables
    -- = Var Name Int -- x
    -- | Ref Name     -- x
    -- | Sub Term     -- x
    Var k i -> do
      uses <- get
      case M.lookup k uses of
        Just 0  -> do
          modify (M.insert k 1)
          pure ()
        Just n  -> lift $ TerminationFail (NonlinearVar (Var k i))
        Nothing -> lift $ TerminationFail (UnknownTermination (Var k i))
    Ref name -> terminatesM book (Var name 0)
    Sub term -> terminatesM book term

    -- -- Definitions
    -- | Fix Name Body -- μx. f
    Fix x f -> do
      let atMostStructural = testStructural x False (f (Var x 0))
      let msg = trace (show atMostStructural ++ " = testStructural") ()
      msg `seq` pure ()
      if atMostStructural
        then pure ()
        else lift $ TerminationFail (NonstructuralRecursion term)

    -- | Let Term Term -- !v; f
    Let (Var x i) f -> do
      modify (M.insert x 0)
      terminatesM book f
    Let (Chk (Var x i) t) f -> do
      modify (M.insert x 0)
      terminatesM book f
    Let _ f -> error "(Let not-var ...) not supported in terminates"

    -- -- Universe
    -- | Set -- Set
    Set -> pure ()

    -- -- Annotation
    -- | Ann Term Type -- <x:t>
    Ann term typ -> terminatesM book term

    -- | Chk Term Type -- x::t
    Chk term typ -> terminatesM book term

    -- -- Empty
    -- | Emp -- ⊥
    Emp -> pure ()

    -- | Efq -- λ{}
    Efq -> pure ()

    -- -- Unit
    -- | Uni      -- ⊤
    Uni -> pure ()

    -- | One      -- ()
    One -> pure ()

    -- | Use Term -- λ{():f}
    Use term -> terminatesM book term

    -- -- Bool
    -- | Bit           -- Bool
    Bit -> pure ()

    -- | Bt0           -- False
    Bt0 -> pure ()

    -- | Bt1           -- True
    Bt1 -> pure ()

    -- | Bif Term Term -- λ{False:f;True:t}
    Bif f t -> do
      terminatesM book f
      terminatesM book t

    -- -- Nat
    -- | Nat           -- Nat
    Nat -> pure ()

    -- | Zer           -- 0
    Zer -> pure ()

    -- | Suc Term      -- ↑n
    Suc n -> terminatesM book n

    -- | Swi Term Term -- λ{0:z;+:s}
    Swi z s -> do
      terminatesM book z
      terminatesM book s

    -- -- List
    -- | Lst Type      -- T[]
    Lst typ -> pure ()

    -- | Nil           -- []
    Nil -> pure ()

    -- | Con Term Term -- h<>t
    Con h t -> do
      terminatesM book h
      terminatesM book t

    -- | Mat Term Term -- λ{[]:n;<>:c}
    Mat n c -> do
      terminatesM book n
      terminatesM book c

    -- -- Enum
    -- | Enu [String]        -- {'foo','bar'...}
    Enu _ -> pure ()

    -- | Sym String          -- 'foo'
    Sym _ -> pure ()

    -- | Cse [(String,Term)] -- λ{'foo':f;'bar':b;...}
    Cse cases -> mapM_ (terminatesM book . snd) cases

    -- -- Pair
    -- | Sig Type Type -- ΣA.B
    Sig a b -> pure ()

    -- | Tup Term Term -- (a,b)
    Tup a b -> do
      terminatesM book a
      terminatesM book b

    -- | Get Term      -- λ{(,):f}
    Get f -> terminatesM book f

    -- -- Function
    -- | All Type Type -- ∀A.B
    All a b -> pure ()

    -- | Lam Name Body -- λx.f
    Lam x f -> do
      modify (M.insert x 0)
      terminatesM book (f (Var x 0))

    -- | App Term Term -- (f x)
    App f x -> do
      terminatesM book f
      terminatesM book x

    -- -- Equality
    -- | Eql Type Term Term -- T{a==b}
    Eql typ a b -> do
      terminatesM book a
      terminatesM book b

    -- | Rfl                -- {=}
    Rfl -> pure ()

    -- | Rwt Term           -- λ{{=}:f}
    Rwt f -> terminatesM book f

    -- -- MetaVar
    -- | Met Int Type [Term] -- ?N:T{x0,x1,...}
    Met _ typ args -> mapM_ (terminatesM book) args

    -- -- Hints
    -- | Ind Type -- ~T
    Ind typ -> pure ()

    -- | Frz Type -- ∅T
    Frz typ -> pure ()

    -- -- Supperpositions
    -- | Era               -- *
    Era -> pure ()

    -- | Sup Int Term Term -- &L{a,b}
    Sup _ a b -> do
      terminatesM book a
      terminatesM book b

    -- Pattern-Match
    -- match x y ...:
    --   with a=r with b=s ...
    --   case (A ...) (B ...): ...
    --   case (C ...) (D ...): ...
    Pat terms moves cases -> do
      let flattened = flatten (Pat terms moves cases)
      terminatesM book flattened

implies :: Bool -> Bool -> Bool
implies a b = not (a && not b)
-- implies a b = a
-- implies a b = b

testStructural :: Name -> Bool -> Term -> Bool
testStructural name hasEliminatedConstr (Var k i)      = implies (name == k) hasEliminatedConstr
testStructural name hasEliminatedConstr (Ref k)        = implies (name == k) hasEliminatedConstr
testStructural name hasEliminatedConstr (Sub t)        = False
testStructural name hasEliminatedConstr (Fix k f)      = testStructural name hasEliminatedConstr (f (Var k 0))
testStructural name hasEliminatedConstr (Let v f)      = case f of
  (Lam k f) -> testStructural name hasEliminatedConstr v || testStructural name hasEliminatedConstr (f (Var k 0))
  _         -> testStructural name hasEliminatedConstr v || testStructural name hasEliminatedConstr f
testStructural name hasEliminatedConstr (Set)          = False
testStructural name hasEliminatedConstr (Ann x t)      = testStructural name hasEliminatedConstr x
testStructural name hasEliminatedConstr (Chk x t)      = testStructural name hasEliminatedConstr x
testStructural name hasEliminatedConstr (Emp)          = False
testStructural name hasEliminatedConstr (Efq)          = False
testStructural name hasEliminatedConstr (Uni)          = False
testStructural name hasEliminatedConstr (One)          = False
testStructural name hasEliminatedConstr (Use f)        = testStructural name True f
testStructural name hasEliminatedConstr (Bit)          = False
testStructural name hasEliminatedConstr (Bt0)          = False
testStructural name hasEliminatedConstr (Bt1)          = False
testStructural name hasEliminatedConstr (Bif f t)      = testStructural name True f
testStructural name hasEliminatedConstr (Nat)          = False
testStructural name hasEliminatedConstr (Zer)          = False
testStructural name hasEliminatedConstr (Suc n)        = testStructural name hasEliminatedConstr n
testStructural name hasEliminatedConstr (Swi z s)      = testStructural name True z || testStructural name True s
testStructural name hasEliminatedConstr (Lst t)        = testStructural name hasEliminatedConstr t
testStructural name hasEliminatedConstr (Nil)          = False
testStructural name hasEliminatedConstr (Con h t)      = testStructural name hasEliminatedConstr h || testStructural name hasEliminatedConstr t
testStructural name hasEliminatedConstr (Mat n c)      = testStructural name True n || testStructural name True c
testStructural name hasEliminatedConstr (Enu s)        = False
testStructural name hasEliminatedConstr (Sym s)        = False
testStructural name hasEliminatedConstr (Cse c)        = any (testStructural name True . snd) c
testStructural name hasEliminatedConstr (Sig a b)      = case b of
  (Lam k f) -> testStructural name hasEliminatedConstr a || testStructural name hasEliminatedConstr (f (Var k 0))
  _         -> testStructural name hasEliminatedConstr a || testStructural name hasEliminatedConstr b
testStructural name hasEliminatedConstr (Tup a b)      = testStructural name hasEliminatedConstr a || testStructural name hasEliminatedConstr b
testStructural name hasEliminatedConstr (Get f)        = testStructural name hasEliminatedConstr f
testStructural name hasEliminatedConstr (All a b)      = case b of
  (Lam k f) -> testStructural name hasEliminatedConstr a || testStructural name hasEliminatedConstr (f (Var k 0))
  _         -> testStructural name hasEliminatedConstr a || testStructural name hasEliminatedConstr b
testStructural name hasEliminatedConstr (Lam k f)      = testStructural name hasEliminatedConstr (f (Var k 0))
testStructural name hasEliminatedConstr (App f x)      = testStructural name hasEliminatedConstr f || testStructural name hasEliminatedConstr x
testStructural name hasEliminatedConstr (Eql t a b)    = testStructural name hasEliminatedConstr t || testStructural name hasEliminatedConstr a || testStructural name hasEliminatedConstr b
testStructural name hasEliminatedConstr (Rfl)          = False
testStructural name hasEliminatedConstr (Rwt f)        = testStructural name True f
testStructural name hasEliminatedConstr (Ind t)        = testStructural name hasEliminatedConstr t
testStructural name hasEliminatedConstr (Frz t)        = testStructural name hasEliminatedConstr t
testStructural name hasEliminatedConstr (Era)          = False
testStructural name hasEliminatedConstr (Sup l a b)    = testStructural name hasEliminatedConstr a || testStructural name hasEliminatedConstr b
testStructural name hasEliminatedConstr (Met n ty ts)  = testStructural name hasEliminatedConstr ty || any (testStructural name hasEliminatedConstr) ts
testStructural name hasEliminatedConstr (Pat s m c)    = any (testStructural name hasEliminatedConstr) s || any (testStructural name hasEliminatedConstr . snd) m || any (testStructural name hasEliminatedConstr . snd) c
