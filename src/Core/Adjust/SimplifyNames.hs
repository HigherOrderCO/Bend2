module Core.Adjust.SimplifyNames where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List (intercalate, isPrefixOf)
import Data.List.Split (splitOn)
import Data.Maybe (fromMaybe)
import Control.Monad (foldM)
import Control.Exception (throw)

import Debug.Trace

import Core.Type
import Core.Show

variationsMap :: Book -> CountMap 
variationsMap book@(Book defs nams _) = (refCounts, symCounts)
  where
    refCounts = condense $ S.fromList nams
    symCounts = condense $ foldl (\counts (_,trm,typ) -> foldl S.union S.empty [go S.empty trm, go S.empty typ,counts]) S.empty defs
    
    -- Counts how many fully qualified names correspond to each sugared name
    condense :: S.Set Name -> M.Map Name Int
    condense names = foldl (\counts name -> M.unionWith (\c1 c2 -> c1+c2) counts (M.singleton name 1)) M.empty (map cutName (S.toList names))

    -- Collects all fully qualified Sym strings declared in Enu's of a term
    go :: S.Set Name -> Term -> S.Set Name 
    go seen term = case term of
      -- Variables
      Var k i      -> S.empty
      Ref k _      -> S.empty
      Sub t        -> go seen t

      -- IO type
      IO t         -> go seen t

      -- Definitions
      Fix k f      -> go seen (f (Var k 0))
      Let k mt v f -> foldl S.union S.empty [maybe S.empty (go seen) mt, go seen v, go seen (f (Var k 0))]
      Use k v f    -> foldl S.union S.empty [go seen v, go seen (f (Var k 0))]

      -- Universe
      Set          -> S.empty

      -- Annotation
      Chk x t      -> foldl S.union S.empty [go seen x, go seen t]
      Tst x        -> go seen x

      -- Empty
      Emp          -> S.empty
      EmpM         -> S.empty

      -- Unit
      Uni          -> S.empty
      One          -> S.empty
      UniM f       -> go seen f

      -- Bool
      Bit          -> S.empty
      Bt0          -> S.empty
      Bt1          -> S.empty
      BitM f t     -> S.empty

      -- Nat
      Nat          -> S.empty
      Zer          -> S.empty
      Suc n        -> go seen n
      NatM z s     -> foldl S.union S.empty [go seen z, go seen s]

      -- List
      Lst t        -> go seen t
      Nil          -> S.empty
      Con h t      -> foldl S.union S.empty [go seen h, go seen t]
      LstM n c     -> foldl S.union S.empty [go seen n, go seen c]

      -- Enum
      Enu s        -> S.fromList s
      Sym s        -> S.empty
      EnuM cs d'   -> S.empty

      -- Numbers
      Num t        -> S.empty
      Val v        -> S.empty
      Op2 o a b    -> foldl S.union S.empty [go seen a, go seen b]
      Op1 o a      -> go seen a

      -- Pair
      Sig a b      -> foldl S.union S.empty [go seen a, go seen b]
      Tup a b      -> foldl S.union S.empty [go seen a, go seen b]
      SigM f       -> go seen f

      -- Function
      All a b      -> foldl S.union S.empty [go seen a, go seen b]
      Lam k mt f   -> go seen (f (Var k 0))
      App f x      -> foldl S.union S.empty [go seen f, go seen x]

      -- Equality
      Eql t a b    -> foldl S.union S.empty [go seen t, go seen a, go seen b]
      Rfl          -> S.empty
      EqlM f       -> go seen f
      Rwt e f      -> foldl S.union S.empty [go seen e, go seen f]

      -- MetaVar
      Met n t ctx  -> foldl S.union S.empty [go seen t, foldl (\co tr -> S.union co (go seen tr)) S.empty ctx]

      -- Supperpositions
      Era          -> S.empty
      Sup l a b    -> foldl S.union S.empty [go seen l, go seen a, go seen b]
      SupM l f     -> foldl S.union S.empty [go seen l, go seen f]

      -- Errors
      Loc _ t      -> go seen t

      -- Logging
      Log s x      -> foldl S.union S.empty [go seen s, go seen x]

      -- Primitive
      Pri p        -> S.empty

      -- Sugars
      Pat ts ms cs -> foldl S.union S.empty [fromTs, fromMs, fromCs]
        where
          fromTs = foldl (\co      tr  -> S.union co (go seen tr)) S.empty ts
          fromMs = foldl (\co (_  ,tr) -> S.union co (go seen tr)) S.empty ms
          fromCs = foldl (\co (trs,tr) -> foldl S.union S.empty [co, foldl S.union S.empty (map (go seen) trs),go seen tr]) S.empty cs
      Frk l a b    -> foldl S.union S.empty [go seen l, go seen a, go seen b]
