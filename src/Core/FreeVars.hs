module Core.FreeVars where

import Core.Type
import qualified Data.Set as S

-- | Returns the free variables in a term by name.
freeVars :: S.Set Name -> Term -> S.Set Name
freeVars ctx tm = case tm of
  Var n _     -> if n `S.member` ctx then S.empty else S.singleton n
  Sub t       -> freeVars ctx t
  Fix n f     -> freeVars (S.insert n ctx) (f (Var n 0))
  Let k t v f -> S.unions [foldMap (freeVars ctx) t, freeVars ctx v, freeVars (S.insert k ctx) (f (Var k 0))]
  Use k v f   -> S.union (freeVars ctx v) (freeVars (S.insert k ctx) (f (Var k 0)))
  Chk v t     -> S.union (freeVars ctx v) (freeVars ctx t)
  UniM f      -> freeVars ctx f
  BitM f t    -> S.union (freeVars ctx f) (freeVars ctx t)
  Suc n       -> freeVars ctx n
  NatM z s    -> S.union (freeVars ctx z) (freeVars ctx s)
  Lst t       -> freeVars ctx t
  Con h t     -> S.union (freeVars ctx h) (freeVars ctx t)
  LstM n c    -> S.union (freeVars ctx n) (freeVars ctx c)
  EnuM c e    -> S.union (S.unions (map (freeVars ctx . snd) c)) (freeVars ctx e)
  Op2 _ a b   -> S.union (freeVars ctx a) (freeVars ctx b)
  Op1 _ a     -> freeVars ctx a
  Sig a b     -> S.union (freeVars ctx a) (freeVars ctx b)
  Tup a b     -> S.union (freeVars ctx a) (freeVars ctx b)
  SigM f      -> freeVars ctx f
  All a b     -> S.union (freeVars ctx a) (freeVars ctx b)
  Lam n t f   -> S.union (freeVars (S.insert n ctx) (f (Var n 0))) (foldMap (freeVars ctx) t)
  App f x     -> S.union (freeVars ctx f) (freeVars ctx x)
  Eql t a b   -> S.unions [freeVars ctx t, freeVars ctx a, freeVars ctx b]
  EqlM f      -> freeVars ctx f
  Rwt e f     -> S.union (freeVars ctx e) (freeVars ctx f)
  Met _ t c   -> S.unions (freeVars ctx t : map (freeVars ctx) c)
  Sup _ a b   -> S.union (freeVars ctx a) (freeVars ctx b)
  SupM l f    -> S.union (freeVars ctx l) (freeVars ctx f)
  Frk l a b   -> S.unions [freeVars ctx l, freeVars ctx a, freeVars ctx b]
  Log s x     -> S.union (freeVars ctx s) (freeVars ctx x)
  Loc _ t     -> freeVars ctx t
  Pat s m c   -> S.unions ((map (freeVars ctx) s) ++ (map (\(_,m) -> freeVars ctx m) m) ++ (map (\(_,c) -> freeVars ctx c) c))
  _           -> S.empty
