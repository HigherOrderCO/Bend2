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

--
-- simplifyNames :: Book -> Book
-- simplifyNames book@(Book defs nams) = Book newDefs newNames
-- -- simplifyNames book@(Book defs nams) = trace ("[variations] " ++ show (variationsMap book)) $ book
--   where
--     variations@(refVariations, symVariations) = variationsMap book
--     simplifyName count name@('?':'0':_) = name
--     simplifyName count name@('?':'1':_) = name
--     simplifyName count name = case M.lookup (shortName name) count of
--       Just n | n > 1 -> 
--         -- trace ("[" ++ name ++ "] -> " ++ show ("0" ++ name)) $ 
--           "?0" ++ name
--       _              -> 
--         -- trace ("[" ++ name ++ "] -> " ++ show ("1" ++ name)) $ 
--           "?1" ++ name
--
--     newNames = map (simplifyName refVariations) nams
--     newDefs = M.fromList $ map (\(nam, (inj, term, typ)) -> (simplifyName refVariations nam, (inj, go term, go typ))) (M.toList defs)
--
--     go term = case term of
--       -- Variables
--       Var k i      -> Var k i
--       Ref k i      -> Ref (simplifyName refVariations k) i
--       Sub t        -> Sub (go t)
--
--       -- IO type
--       IO t         -> IO (go t)
--
--       -- Definitions
--       Fix k f      -> Fix k (\x -> go (f x))
--       Let k mt v f -> Let k (fmap go mt) (go v) (\x -> go (f x))
--       Use k v f    -> Use k (go v) (\x -> go (f x))
--
--       -- Universe
--       Set          -> term
--
--       -- Annotation
--       Chk x t      -> Chk (go x) (go t)
--       Tst x        -> Tst (go x)
--
--       -- Empty
--       Emp          -> term
--       EmpM         -> term
--
--       -- Unit
--       Uni          -> term
--       One          -> term
--       UniM f       -> UniM (go f)
--
--       -- Bool
--       Bit          -> term
--       Bt0          -> term
--       Bt1          -> term
--       BitM f t     -> BitM (go f) (go t)
--
--       -- Nat
--       Nat          -> term
--       Zer          -> term
--       Suc n        -> Suc (go n)
--       NatM z s     -> NatM (go z) (go s)
--
--       -- List
--       Lst t        -> Lst (go t)
--       Nil          -> term
--       Con h t      -> Con (go h) (go t)
--       LstM n c     -> LstM (go n) (go c)
--
--       -- Enum
--       Enu s        -> Enu (map (simplifyName symVariations) s)
--       -- Enu s        -> Enu s
--       Sym s        -> Sym (simplifyName symVariations s)
--       EnuM cs d'   -> EnuM (map (\(s,t) -> (simplifyName symVariations s, go t)) cs) (go d')
--
--       -- Numbers
--       Num t        -> term
--       Val v        -> term
--       Op2 o a b    -> Op2 o (go a) (go b)
--       Op1 o a      -> Op1 o (go a)
--
--       -- Pair
--       Sig a b      -> Sig (go a) (go b)
--       Tup a b      -> Tup (go a) (go b)
--       SigM f       -> SigM (go f)
--
--       -- Function
--       All a b      -> All (go a) (go b)
--       Lam k mt f   -> Lam k (fmap go mt) (\x -> go (f x))
--       App f x      -> App (go f) (go x)
--
--       -- Equality
--       Eql t a b    -> Eql (go t) (go a) (go b)
--       Rfl          -> term
--       EqlM f       -> EqlM (go f)
--       Rwt e f      -> Rwt (go e) (go f)
--
--       -- MetaVar
--       Met n t ctx  -> Met n (go t) (map go ctx)
--
--       -- Supperpositions
--       Era          -> term
--       Sup l a b    -> Sup (go l) (go a) (go b)
--       SupM l f     -> SupM (go l) (go f)
--
--       -- Errors
--       Loc s t      -> Loc s (go t)
--
--       -- Logging
--       Log s x      -> Log (go s) (go x)
--
--       -- Primitive
--       Pri p        -> term
--
--       -- Sugars
--       Pat ts ms cs -> Pat fromTs fromMs fromCs
--         where
--           fromTs = map go ts
--           fromMs = map (\(s ,t) -> (s, t)) ms
--           fromCs = map (\(ts,t) -> (map go ts, go t)) cs
--       Frk l a b    -> Frk (go l) (go a) (go b)
--
--

variationsMap :: Book -> CountMap 
variationsMap book@(Book defs nams _) =
  foldl mergeCounts initialCounts (map (\(_,(_,term,typ)) -> mergeCounts (go 0 emptyCount term) (go 0 emptyCount typ)) (M.toList defs))
  where
    emptyCount = (M.empty,M.empty)
  
    initialCounts :: CountMap
    initialCounts = (M.fromList $ map (\nam -> (cutName nam, 1)) nams, M.empty)

    mergeCounts :: CountMap -> CountMap -> CountMap
    mergeCounts (refCountA, symCountA) (refCountB, symCountB) = (merge refCountA refCountB, merge symCountA symCountB)
      where
        merge a b = M.unionWith (\c1 c2 -> c1+c2) a b

    go :: Int -> CountMap -> Term -> CountMap
    go d count term = case term of
      -- Variables
      Var k i      -> emptyCount
      Ref k _      -> emptyCount
      Sub t        -> go d count t

      -- IO type
      IO t         -> go d count t

      -- Definitions
      Fix k f      -> go (d+1) count (f (Var k d))
      Let k mt v f -> foldl mergeCounts emptyCount [maybe emptyCount (go d count) mt, go d count v, go (d+1) count (f (Var k d))]
      Use k v f    -> foldl mergeCounts emptyCount [go d count v, go d count (f (Var k d))]

      -- Universe
      Set          -> emptyCount

      -- Annotation
      Chk x t      -> foldl mergeCounts emptyCount [go d count x, go d count t]
      Tst x        -> go d count x

      -- Empty
      Emp          -> emptyCount
      EmpM         -> emptyCount

      -- Unit
      Uni          -> emptyCount
      One          -> emptyCount
      UniM f       -> go d count f

      -- Bool
      Bit          -> emptyCount
      Bt0          -> emptyCount
      Bt1          -> emptyCount
      BitM f t     -> emptyCount

      -- Nat
      Nat          -> emptyCount
      Zer          -> emptyCount
      Suc n        -> go d count n
      NatM z s     -> foldl mergeCounts emptyCount [go d count z, go d count s]

      -- List
      Lst t        -> go d count t
      Nil          -> emptyCount
      Con h t      -> foldl mergeCounts emptyCount [go d count h, go d count t]
      LstM n c     -> foldl mergeCounts emptyCount [go d count n, go d count c]

      -- Enum
      Enu s        -> mergeCounts count (M.empty,(M.fromList $ map (\s -> (cutName s,1)) s))
      Sym s        -> emptyCount
      EnuM cs d'   -> emptyCount

      -- Numbers
      Num t        -> emptyCount
      Val v        -> emptyCount
      Op2 o a b    -> foldl mergeCounts emptyCount [go d count a, go d count b]
      Op1 o a      -> go d count a

      -- Pair
      Sig a b      -> foldl mergeCounts emptyCount [go d count a, go d count b]
      Tup a b      -> foldl mergeCounts emptyCount [go d count a, go d count b]
      SigM f       -> go d count f

      -- Function
      All a b      -> foldl mergeCounts emptyCount [go d count a, go d count b]
      Lam k mt f   -> go (d+1) count (f (Var k d))
      App f x      -> foldl mergeCounts emptyCount [go d count f, go d count x]

      -- Equality
      Eql t a b    -> foldl mergeCounts emptyCount [go d count t, go d count a, go d count b]
      Rfl          -> emptyCount
      EqlM f       -> go d count f
      Rwt e f      -> foldl mergeCounts emptyCount [go d count e, go d count f]

      -- MetaVar
      Met n t ctx  -> foldl mergeCounts emptyCount [go d count t, foldl (\co tr -> mergeCounts co (go d count tr)) emptyCount ctx]

      -- Supperpositions
      Era          -> emptyCount
      Sup l a b    -> foldl mergeCounts emptyCount [go d count l, go d count a, go d count b]
      SupM l f     -> foldl mergeCounts emptyCount [go d count l, go d count f]

      -- Errors
      Loc _ t      -> go d count t

      -- Logging
      Log s x      -> foldl mergeCounts emptyCount [go d count s, go d count x]

      -- Primitive
      Pri p        -> emptyCount

      -- Sugars
      Pat ts ms cs -> foldl mergeCounts emptyCount [fromTs, fromMs, fromCs]
        where
          fromTs = foldl (\co      tr  -> mergeCounts co (go d count tr)) emptyCount ts
          fromMs = foldl (\co (_  ,tr) -> mergeCounts co (go d count tr)) emptyCount ms
          fromCs = foldl (\co (trs,tr) -> foldl mergeCounts emptyCount [co, foldl mergeCounts emptyCount (map (go d count) trs),go d count tr]) emptyCount cs
      Frk l a b    -> foldl mergeCounts emptyCount [go d count l, go d count a, go d count b]
      
