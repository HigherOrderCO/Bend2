{-./Type.hs-}
{-./WHNF.hs-}
{-./Equal.hs-}

module Core.BigRewrite where

import System.IO.Unsafe
import Data.IORef
import Data.Bits
import qualified Data.Set as S
import GHC.Float (castDoubleToWord64, castWord64ToDouble)

import Core.BigEqual
import Core.Type
import Core.WHNF
import Core.Show

import Debug.Trace

-- Rewrite
-- =======

rewrite :: Int -> Book -> Term -> Term -> Term -> Term
rewrite d book old neo val
  | equal d book old val = neo
  | otherwise            = rewriteGo d book S.empty old neo $ whnf book val

rewriteGo :: Int -> Book -> S.Set Name -> Term -> Term -> Term -> Term
rewriteGo d book seen old neo val
  -- | trace ("REWRITE EQ 0 " ++ show val ++ " SEEN: " ++ show seen ++ " CHANGE " ++ show old ++ " -> " ++ show neo) $ equal d book old val = trace ("REWRITE GO 0 " ++ show val ++ " SEEN: " ++ show seen ++ " CHANGE " ++ show old ++ " -> " ++ show neo) $ neo
  | trace ("REWRITE EQ 0 " ++ show val ++ " SEEN: " ++ show seen ++ " CHANGE " ++ show old ++ " -> " ++ show neo) $ equal d book old val = trace ("REWRITE GO 0 " ++ show val ++ " SEEN: " ++ show seen ++ " CHANGE " ++ show old ++ " -> " ++ show neo) $ neo
  -- | otherwise            = rewriteGoGo d book seen old neo $ whnf book val
  | otherwise            = case cut val of 
    App f x -> 
      let (fn,xs) = collectApps (App f x) []
      in case fn of
        Ref k _ -> if k `elem` seen
                   then trace ("REWRITE GO 1 " ++ show val ++ " SEEN: " ++ show seen ++ " CHANGE " ++ show old ++ " -> " ++ show neo) $ foldl (\ f x -> App f (rewriteGo d book seen old neo x)) fn xs
                   else trace ("REWRITE GO 2 " ++ show val ++ " SEEN: " ++ show seen ++ " CHANGE " ++ show old ++ " -> " ++ show neo) $ rewriteGoGo d book (S.insert k seen) old neo $ whnf book val
        _       -> trace ("REWRITE GO 3 " ++ show val ++ " SEEN: " ++ show seen ++ " CHANGE " ++ show old ++ " -> " ++ show neo) $ rewriteGoGo d book seen old neo $ whnf book val
    _       -> trace ("REWRITE GO 4 " ++ show val ++ " SEEN: " ++ show seen ++ " CHANGE " ++ show old ++ " -> " ++ show neo) $ rewriteGoGo d book seen old neo $ whnf book val

-- Recursively rewriteGos occurrences of 'old' with 'neo' in 'val'
rewriteGoGo :: Int -> Book -> S.Set Name -> Term -> Term -> Term -> Term
rewriteGoGo d book seen old neo val =
  trace ("REWRITE GOGO " ++ show val ++ " SEEN: " ++ show seen ++ " CHANGE " ++ show old ++ " -> " ++ show neo) $
  case val of
    Var k i     -> Var k i
    Ref k i     -> Ref k i
    Sub t       -> t
    Fix k f     -> Fix k (\x -> rewriteGo (d+1) book seen old neo (f (Sub x)))
    Let k t v f -> Let k (fmap (rewriteGo d book seen old neo) t) (rewriteGo d book seen old neo v) (\x -> rewriteGo (d+1) book seen old neo (f (Sub x)))
    Use k v f   -> Use k (rewriteGo d book seen old neo v) (\x -> rewriteGo d book seen old neo (f (Sub x)))
    Set         -> Set
    Chk x t     -> Chk (rewriteGo d book seen old neo x) (rewriteGo d book seen old neo t)
    Tst x       -> Tst (rewriteGo d book seen old neo x)
    Emp         -> Emp
    EmpM        -> EmpM
    Uni         -> Uni
    One         -> One
    UniM f      -> UniM (rewriteGo d book seen old neo f)
    Bit         -> Bit
    Bt0         -> Bt0
    Bt1         -> Bt1
    BitM f t    -> BitM (rewriteGo d book seen old neo f) (rewriteGo d book seen old neo t)
    Nat         -> Nat
    Zer         -> Zer
    Suc n       -> Suc (rewriteGo d book seen old neo n)
    NatM z s    -> NatM (rewriteGo d book seen old neo z) (rewriteGo d book seen old neo s)
    Lst t       -> Lst (rewriteGo d book seen old neo t)
    Nil         -> Nil
    Con h t     -> Con (rewriteGo d book seen old neo h) (rewriteGo d book seen old neo t)
    LstM n c    -> LstM (rewriteGo d book seen old neo n) (rewriteGo d book seen old neo c)
    Enu s       -> Enu s
    Sym s       -> Sym s
    EnuM c e    -> EnuM (map (\(s,t) -> (s, rewriteGo d book seen old neo t)) c) (rewriteGo d book seen old neo e)
    Num t       -> Num t
    Val v       -> Val v
    Op2 o a b   -> Op2 o (rewriteGo d book seen old neo a) (rewriteGo d book seen old neo b)
    Op1 o a     -> Op1 o (rewriteGo d book seen old neo a)
    Sig a b     -> Sig (rewriteGo d book seen old neo a) (rewriteGo d book seen old neo b)
    Tup a b     -> Tup (rewriteGo d book seen old neo a) (rewriteGo d book seen old neo b)
    SigM f      -> SigM (rewriteGo d book seen old neo f)
    All a b     -> All (rewriteGo d book seen old neo a) (rewriteGo d book seen old neo b)
    -- Lam k t f   -> Lam k (fmap (rewriteGo d book seen old neo) t) (\v -> rewriteGo (d+1) book seen old neo (f v))
    Lam k t f   -> Lam k (fmap (rewriteGo d book seen old neo) t) (\v -> rewriteGo (d+1) book seen old neo (f (Sub v)))
    App f x     -> App (rewriteGo d book seen old neo f) (rewriteGo d book seen old neo x)
    Eql t a b   -> Eql (rewriteGo d book seen old neo t) (rewriteGo d book seen old neo a) (rewriteGo d book seen old neo b)
    Rfl         -> Rfl
    EqlM f      -> EqlM (rewriteGo d book seen old neo f)
    Rwt e f     -> Rwt (rewriteGo d book seen old neo e) (rewriteGo d book seen old neo f)
    Met i t a   -> Met i (rewriteGo d book seen old neo t) (map (rewriteGo d book seen old neo) a)
    Era         -> Era
    Sup l a b   -> Sup l (rewriteGo d book seen old neo a) (rewriteGo d book seen old neo b)
    SupM l f    -> SupM (rewriteGo d book seen old neo l) (rewriteGo d book seen old neo f)
    Frk l a b   -> Frk (rewriteGo d book seen old neo l) (rewriteGo d book seen old neo a) (rewriteGo d book seen old neo b)
    Loc s t     -> Loc s (rewriteGo d book seen old neo t)
    Log s x     -> Log (rewriteGo d book seen old neo s) (rewriteGo d book seen old neo x)
    Pri p       -> Pri p
    Pat t m c   -> Pat (map (rewriteGo d book seen old neo) t) (map (\(k,v) -> (k, rewriteGo d book seen old neo v)) m) (map (\(ps,v) -> (map (rewriteGo d book seen old neo) ps, rewriteGo d book seen old neo v)) c)

rewriteCtx :: Int -> Book -> Term -> Term -> Ctx -> Ctx
rewriteCtx d book old neo (Ctx ctx) = Ctx (map rewriteGoAnn ctx)
  where rewriteGoAnn (k,v,t) = (k, v, rewrite d book old neo t)
