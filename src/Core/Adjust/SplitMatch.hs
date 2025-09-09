{-# LANGUAGE ViewPatterns #-}

module Core.Adjust.SplitMatch where

import Core.Bind
import Core.BigCheck
import Core.FreeVars
import Core.Show
import Core.Type
import Core.WHNF
import qualified Data.Set as S
import Debug.Trace (trace)

reWrap :: Term -> Term -> Term
reWrap (Loc l _) z = Loc l z
reWrap (Chk x t) z = Chk z t
reWrap _        z = z

cutLoc :: Term -> Term
cutLoc (Loc l t) = t
cutLoc t         = t

isMatch :: Term -> Bool
isMatch (Loc _ f) = isLam f
isMatch EmpM      = True
isMatch UniM{}    = True
isMatch BitM{}    = True
isMatch NatM{}    = True
isMatch LstM{}    = True
isMatch EnuM{}    = True
isMatch SigM{}    = True
isMatch SupM{}    = True
isMatch EqlM{}    = True
isMatch _         = False

isVar :: Term -> Bool
isVar Var{} = True
isVar _     = False

split :: Int -> Int -> Term -> Term
split d aux (App f x) = 
  let f' = split d aux f
      x' = split d aux x
  in
  case cutLoc f' of
    (Chk f'' t) | isMatch (cut f'') && not (isVar $ cut x') -> Let ("$aux_" ++ show aux) (Just t) f'' (\v -> App v x')
    _                                                       -> App f' x' 
split d aux (Log l t)     = Log (split d aux l) (split d aux t)
split d aux (Loc l t)     = Loc l (split d aux t)
split d aux (Lam k mt b)  = Lam k mt (\x -> split (d+1) aux (b (Sub x)))
split d aux (UniM f)      = UniM (split d aux f)
split d aux (BitM f t)    = BitM (split d aux f) (split d aux t)
split d aux (NatM z s)    = NatM (split d aux z) (split d aux s)
split d aux (SigM g)      = SigM (split d aux g)
split d aux (Var k i)     = Var k i
split d aux (Ref k i)     = Ref k i
split d aux (Sub t)       = t
split d aux (Fix k f)     = Fix k (\x -> split (d+1) aux (f (Sub x)))
split d aux (Let k t v f) = Let k (fmap (split d aux) t) (split d aux v) (\x -> split (d+1) aux (f (Sub x)))
split d aux (Use k v f)   = Use k (split d aux v) (\x -> split (d+1) aux (f (Sub x)))
split d aux Set           = Set
split d aux (Chk x t)     = Chk (split d aux x) (split d aux t)
split d aux (Tst x)       = Tst (split d aux x)
split d aux Emp           = Emp
split d aux EmpM          = EmpM
split d aux Uni           = Uni
split d aux One           = One
split d aux Bit           = Bit
split d aux Bt0           = Bt0
split d aux Bt1           = Bt1
split d aux Nat           = Nat
split d aux Zer           = Zer
split d aux (Suc n)       = Suc (split d aux n)
split d aux (Lst t)       = Lst (split d aux t)
split d aux Nil           = Nil
split d aux (Con h t)     = Con (split d aux h) (split d aux t)
split d aux (LstM n c)    = LstM (split d aux n) (split d aux c)
split d aux (Enu s)       = Enu s
split d aux (Sym s)       = Sym s
split d aux (EnuM c e)    = EnuM [(s, split d aux t) | (s, t) <- c] (split d aux e)
split d aux (Num t)       = Num t
split d aux (Val v)       = Val v
split d aux (Op2 o a b)   = Op2 o (split d aux a) (split d aux b)
split d aux (Op1 o a)     = Op1 o (split d aux a)
split d aux (Sig a b)     = Sig (split d aux a) (split d aux b)
split d aux (Tup a b)     = Tup (split d aux a) (split d aux b)
split d aux (All a b)     = All (split d aux a) (split d aux b)
split d aux (Eql t a b)   = Eql (split d aux t) (split d aux a) (split d aux b)
split d aux Rfl           = Rfl
split d aux (EqlM f)      = EqlM (split d aux f)
split d aux (Rwt e f)     = Rwt (split d aux e) (split d aux f)
split d aux (Met n t x)   = Met n (split d aux t) (map (split d aux) x)
split d aux Era           = Era
split d aux (Sup l a b)   = Sup (split d aux l) (split d aux a) (split d aux b)
split d aux (SupM l f)    = SupM (split d aux l) (split d aux f)
split d aux (Pri p)       = Pri p
split d aux (Pat s m c)   = Pat (map (split d aux) s) 
                                  [(k, split d aux v) | (k, v) <- m] 
                                  [(ps, split d aux b) | (ps, b) <- c]
split d aux (Frk l a b)   = Frk (split d aux l) (split d aux a) (split d aux b)










