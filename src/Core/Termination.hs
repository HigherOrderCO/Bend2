module Core.Termination where

import Control.Applicative (Alternative(..))
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Set (Set)
import Data.Map (Map)
import Debug.Trace

import Core.Type

-- Get immediate subterms of a term
subterms :: Int -> Term -> [Term]
subterms d term = case term of
  Var _ _       -> []
  Ref _ _       -> []
  Sub x         -> [x]
  Fix k b       -> [b (Var k d)]
  Lam x _ b     -> [b (Var x d)]
  Let k t v f   -> maybe [] (:[]) t ++ [v, f (Var k d)]
  Use k v f     -> [v, f (Var k d)]
  Chk v t       -> [v, t]
  Tst v         -> [v]
  Suc n         -> [n]
  Con h t       -> [h, t]
  Tup a b       -> [a, b]
  App f x       -> [f, x]
  Op2 _ a b     -> [a, b]
  Op1 _ a       -> [a]
  Sup _ a b     -> [a, b]
  Frk _ a b     -> [a, b]
  Rwt e f       -> [e, f]
  Loc _ t       -> [t]
  NatM z s      -> [z, s]
  BitM f t      -> [f, t]
  UniM f        -> [f]
  LstM n c      -> [n, c]
  SigM f        -> [f]
  EnuM bs d     -> map snd bs ++ [d]
  SupM l f      -> [l, f]
  Log s x       -> [s, x]
  Pat ms mv cs  -> ms ++ map snd mv ++ concatMap (\(as, b) -> as ++ [b]) cs
  _             -> []

hasSelfRef :: Book -> S.Set String -> String -> Term -> Bool
hasSelfRef book@(Book defs _) visited name (Ref n i)
  | name `elem` visited = True
  | otherwise = any (\(nam, trm) -> hasSelfRef book (S.insert nam visited) name trm) [(nam,trm) | (nam,(_,trm,typ)) <- M.toList defs, nam `elem` visited]
hasSelfRef book visited name term = any (hasSelfRef book visited name) (subterms 0 term)

countVar :: String -> Int -> Term -> Int
countVar vname vlevel term = case term of
  Var k i | k == vname && i == vlevel -> 1
  _ -> sum $ map (countVar vname vlevel) (subterms vlevel term)

checkLinearity :: Int -> Term -> Result ()
checkLinearity d term = case term of
  Lam k _ f -> let body = (f (Var k d))
               in if (countVar k d body <= 1) then checkLinearity (d+1) body else Fail (UnknownTermination term) 
  Fix k b -> let body = b (Var k d)
             in if (countVar k d body <= 1) then checkLinearity (d+1) body else Fail (UnknownTermination term) 
  _ -> sequence_ [checkLinearity d sub | sub <- subterms d term]

isAffineNonRecursive :: Book -> String -> Term -> Map String Int -> Result ()
isAffineNonRecursive book name term _ = if hasSelfRef book (S.insert name S.empty) name term then Fail (UnknownTermination term) else checkLinearity 0 term

-- isInductive :: Term -> Bool
-- isInductive Nat = True
-- isInductive Bit = True
-- isInductive (Lst _) = True
-- isInductive (Enu _) = True
-- isInductive (Sig _ _) = True
-- isInductive (Ind _) = True
-- isInductive (Num _) = True
-- isInductive _ = False

-- isErased :: Term -> Bool
-- isErased (Frz _) = True
-- isErased _ = False

-- unpackAlls :: Term -> ([Term], Term)
-- unpackAlls (All a rest) = let (ps, c) = unpackAlls rest in (a : ps, c)
-- unpackAlls t = ([], t)
--
-- unpackLamsWithLv :: Int -> Term -> ([Term], Term)
-- unpackLamsWithLv lv (Lam k f) = let v = Var k lv
--                                     (ps, b) = unpackLamsWithLv (lv+1) (f v)
--                                     in (v : ps, b)
-- unpackLamsWithLv lv t = ([], t)

-- isProperSubterm :: Term -> Term -> Bool
-- isProperSubterm s t | s == t = False
-- isProperSubterm s t = any (\u -> s == u || isProperSubterm s u) (subterms 0 t)

-- type Smaller = M.Map Int (S.Set Term)

-- checkDecrease :: [Term] -> [Int] -> Smaller -> Int -> Term -> Result ()
-- checkDecrease params indPos smaller lv term = case term of
--   App f x -> let (hd, args) = collectApps term []
--              in case hd of
--                   Ref n | n == (the name) -> if length args /= length params then Fail (UnknownTermination term) else
--                     if not (any (\i -> let a = args !! i
--                                        in a == params !! i || S.member a (M.lookupDefault S.empty i smaller) ) indPos) then Fail (UnknownTermination term) else return ()
--                   _ -> sequence_ [checkDecrease params indPos smaller lv sub | sub <- f : x : []]  -- wait, for App f x, sub are f, x
--   Lam k b -> let body = b (Var k lv)
--              in checkDecrease params indPos smaller (lv+1) body
--   Fix k b -> let body = b (Var k lv)
--              in checkDecrease params indPos smaller (lv+1) body
--   NatM m z s -> do
--     checkDecrease params indPos smaller lv m
--     checkDecrease params indPos smaller lv z
--     case s of
--       Lam k f -> let v = Var k lv
--                      body = f v
--                      newSmaller = foldr (\i acc -> if m == params !! i || S.member m (M.lookupDefault S.empty i smaller) then M.insertWith S.union i (S.singleton v) acc else acc) smaller indPos
--                  in checkDecrease params indPos newSmaller (lv+1) body
--       _ -> checkDecrease params indPos smaller lv s
--   LstM m n c -> do
--     checkDecrease params indPos smaller lv m
--     checkDecrease params indPos smaller lv n
--     case c of
--       Lam h (Lam t b) -> let vh = Var h lv
--                              vt = Var t (lv+1)
--                              body = b vt
--                              newSmaller = foldr (\i acc -> if m == params !! i || S.member m (M.lookupDefault S.empty i smaller) then M.insertWith S.union i (S.singleton vh `S.union` S.singleton vt) acc else acc) smaller indPos
--                              in checkDecrease params indPos newSmaller (lv+2) body
--       _ -> checkDecrease params indPos smaller lv c
--   SigM m f -> do
--     checkDecrease params indPos smaller lv m
--     case f of
--       Lam a (Lam b g) -> let va = Var a lv
--                              vb = Var b (lv+1)
--                              body = g vb
--                              newSmaller = foldr (\i acc -> if m == params !! i || S.member m (M.lookupDefault S.empty i smaller) then M.insertWith S.union i (S.singleton va `S.union` S.singleton vb) acc else acc) smaller indPos
--                              in checkDecrease params indPos newSmaller (lv+2) body
--       _ -> checkDecrease params indPos smaller lv f
--   _ -> sequence_ [checkDecrease params indPos smaller lv sub | sub <- subterms lv term]

-- isStructuralRecursion :: Book -> String -> Term -> Map String Int -> Result ()
-- isStructuralRecursion book name term _ = do
--   let (paramTypes, _) = case deref book name of
--         Just (_, _, typ) -> unpackAlls typ
--         _ -> ([], Set)
--   let indPos = [i | (i, t) <- zip [0..] paramTypes, isInductive t]
--   let (params, body) = unpackLamsWithLv 0 term
--   checkLinearity S.empty 0 term
--   checkDecrease params indPos M.empty 0 body
--
-- isErasedCloning :: Book -> String -> Term -> Map String Int -> Result ()
-- isErasedCloning book name term _ = do
--   let (paramTypes, _) = case deref book name of
--         Just (_, _, typ) -> unpackAlls typ
--         _ -> ([], Set)
--   let indPos = [i | (i, t) <- zip [0..] paramTypes, isInductive t]
--   let allowed = S.fromList [i | (i, t) <- zip [0..] paramTypes, isErased t]
--   let (params, body) = unpackLamsWithLv 0 term
--   checkLinearity allowed 0 term
--   checkDecrease params indPos M.empty 0 body
--
-- isEALInference :: Book -> String -> Term -> Map String Int -> Result ()
-- isEALInference book name term _ = do
--   let (paramTypes, _) = case deref book name of
--         Just (_, _, typ) -> unpackAlls typ
--         _ -> ([], Set)
--   let indPos = [i | (i, t) <- zip [0..] paramTypes, isInductive t]
--   let allowed = S.fromList [i | (i, t) <- zip [0..] paramTypes, not (isInductive t)]
--   let (params, body) = unpackLamsWithLv 0 term
--   checkLinearity allowed 0 term
--   checkDecrease params indPos M.empty 0 body



terminates :: Book -> String -> Term -> Result ()
terminates book name term =
  isAffineNonRecursive book name term M.empty
  -- <|> isStructuralRecursion book name term M.empty
  -- <|> isErasedCloning book name term M.empty
  -- <|> isEALInference book name term M.empty
  -- <|> Fail (UnknownTermination term)
