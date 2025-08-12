module Core.Adjust.Leterize where

import Core.Type
import Core.Show

import Control.Applicative
import Debug.Trace

extend :: Ctx -> Name -> Term -> Term -> Ctx
extend (Ctx ctx) k v t = Ctx (ctx ++ [(k, v, t)])

greedyInfer :: Int -> Book -> Ctx -> Type -> Term -> Type
greedyInfer d book ctx goal term = case term of
  Var n i     -> trace "BBB" undefined
  Ref n i     -> trace "CCC" undefined
  Sub t       -> greedyInfer d book ctx goal t
  Fix k f     -> Fix k (\x -> greedyInfer (d+1) book ctx goal (f x)) -- TODO: think
  Let k ty v f -> greedyInfer d book ctx goal (f v) -- TODO: think
  Use k v f   -> greedyInfer d book ctx goal (f v)  -- TODO: think
  Set         -> Set
  Chk x ty    -> ty
  Emp         -> Set
  EmpM        -> All Emp (Lam "_" Nothing (\_ -> goal)) -- TODO: think
  Uni         -> Set
  One         -> Uni
  UniM f      -> All Uni (UniM (greedyInfer d book ctx goal f))
  Bit         -> Set
  Bt0         -> Bit
  Bt1         -> Bit
  BitM f t    -> All Bit (BitM (greedyInfer d book ctx goal f) (greedyInfer d book ctx goal t)) -- TODO: think
  Nat         -> Set
  Zer         -> Nat
  Suc n       -> Nat
  -- NatM z s    -> All Nat (Lam "_" Nothing (\_ -> NatM (greedyInfer d book ctx goal z) (greedyInfer d book ctx goal s))) -- TODO: think
  NatM z s -> case cut s of
    Lam p mt b -> All Nat (NatM (greedyInfer d book ctx goal z) (Lam p mt (\_ -> (greedyInfer (d+1) book ctx goal (b (Var p d))))))
  Lst ty      -> Set
  Nil         -> undefined
  Con h t     -> Lst (greedyInfer d book ctx goal h)
  LstM n c    -> All (Lst (greedyInfer d book ctx goal n)) (Lam "_" Nothing (\_ -> LstM (greedyInfer d book ctx goal n) (greedyInfer d book ctx goal c))) -- TODO: think
  Enu ss      -> Set
  Sym s       -> undefined
  EnuM cs e   -> EnuM [(s, greedyInfer d book ctx goal v) | (s, v) <- cs] (greedyInfer d book ctx goal e) -- TODO: think
  Num nt      -> Set
  Val nv      -> case nv of
    U64_V _ -> Num U64_T
    I64_V _ -> Num I64_T
    F64_V _ -> Num F64_T
    CHR_V _ -> Num CHR_T
  Op2 o a b   -> Op2 o (greedyInfer d book ctx goal a) (greedyInfer d book ctx goal b) -- TODO: think
  Op1 o a     -> Op1 o (greedyInfer d book ctx goal a)                                 -- TODO: think
  Sig a b     -> Set
  Tup a b     -> Sig (greedyInfer d book ctx goal a) (Lam "_" Nothing (\_ -> greedyInfer d book ctx goal b)) -- TODO: think
  SigM f      -> undefined
  All a b     -> Set
  Lam k ty f  -> trace "AAA" $ undefined
  App f x     -> case greedyInfer d book ctx goal f of
    All a b -> b
    fT      -> goal  -- fallback to goal if not a function type
  Eql ty a b  -> Set
  Rfl         -> undefined
  EqlM f      -> All goal (Lam "_" Nothing (\_ -> goal))  -- pattern match on equality
  Rwt e f     -> greedyInfer d book ctx goal f  -- rewrite maintains the type of f
  Met n ty as -> ty  -- metavariable has its declared type
  Era         -> goal  -- erasure can have any type
  Sup l a b   -> goal  -- superposition inherits the goal type
  SupM l f    -> All goal (Lam "_" Nothing (\_ -> goal))  -- pattern match on superposition
  Loc s t     -> greedyInfer d book ctx goal t  -- location wrapper preserves type
  Log s x     -> greedyInfer d book ctx goal x  -- log preserves the type of x
  Pri p       -> case p of
    U64_TO_CHAR -> All (Num U64_T) (Lam "_" Nothing (\_ -> Num CHR_T))
    CHAR_TO_U64 -> All (Num CHR_T) (Lam "_" Nothing (\_ -> Num U64_T))
    HVM_INC     -> All goal (Lam "_" Nothing (\_ -> goal))
    HVM_DEC     -> All goal (Lam "_" Nothing (\_ -> goal))
  Pat ss ms cs -> goal  -- pattern matching preserves goal type
  Frk l a b   -> goal  -- fork preserves goal type


leterize :: Int -> Int -> Book -> Ctx -> Type -> Term -> Term
leterize d j book ctx typ t = case t of
  Var n i     -> Var n i
  Ref n i     -> Ref n i
  Sub t'      -> Sub (leterize d j book ctx typ t')
  Fix k f     -> Fix k (\x -> leterize (d+1) j book ctx typ (f x))
  Let k ty v f -> Let k (fmap (leterize d j book ctx typ) ty) (leterize d j book ctx typ v) (\x -> leterize (d+1) j book ctx typ (f x))
  Use k v f   -> Use k (leterize d j book ctx typ v) (\x -> leterize (d+1) j book ctx typ (f x))
  Set         -> Set
  Chk x ty    -> Chk (leterize d j book ctx typ x) (leterize d j book ctx typ ty)
  Emp         -> Emp
  EmpM        -> EmpM
  Uni         -> Uni
  One         -> One
  UniM f      -> UniM (leterize d j book ctx typ f)
  Bit         -> Bit
  Bt0         -> Bt0
  Bt1         -> Bt1
  BitM f t    -> BitM (leterize d j book ctx typ f) (leterize d j book ctx typ t)
  Nat         -> Nat
  Zer         -> Zer
  Suc n       -> Suc (leterize d j book ctx typ n)
  NatM z s    -> NatM (leterize d j book ctx typ z) (leterize d j book ctx typ s)
  Lst ty      -> Lst (leterize d j book ctx typ ty)
  Nil         -> Nil
  Con h t'    -> Con (leterize d j book ctx typ h) (leterize d j book ctx typ t')
  LstM n c    -> LstM (leterize d j book ctx typ n) (leterize d j book ctx typ c)
  Enu ss      -> Enu ss
  Sym s       -> Sym s
  EnuM cs e   -> EnuM [(s, leterize d j book ctx typ v) | (s, v) <- cs] (leterize d j book ctx typ e)
  Num nt      -> Num nt
  Val nv      -> Val nv
  Op2 o a b   -> Op2 o (leterize d j book ctx typ a) (leterize d j book ctx typ b)
  Op1 o a     -> Op1 o (leterize d j book ctx typ a)
  Sig a b     -> Sig (leterize d j book ctx typ a) (leterize d j book ctx typ b)
  Tup a b     -> Tup (leterize d j book ctx typ a) (leterize d j book ctx typ b)
  SigM f      -> SigM (leterize d j book ctx typ f)
  All a b     -> All (leterize d j book ctx typ a) (leterize d j book ctx typ b)
  Lam k ty f  -> Lam k (fmap (leterize d j book ctx typ) ty) (\x -> leterize (d+1) j book ctx typ (f x))
  App f x     -> if isLamMatch (cut f)
    then
      let k = "$aux_" ++ show j
          fT = greedyInfer d book ctx typ f
      in
      Let k (Just fT) f (\_ -> App (Var k d) x)
    else App (leterize d j book ctx typ f) (leterize d j book ctx typ x)
  Eql ty a b  -> Eql (leterize d j book ctx typ ty) (leterize d j book ctx typ a) (leterize d j book ctx typ b)
  Rfl         -> Rfl
  EqlM f      -> EqlM (leterize d j book ctx typ f)
  Rwt e f     -> Rwt (leterize d j book ctx typ e) (leterize d j book ctx typ f)
  Met n ty as -> Met n (leterize d j book ctx typ ty) (map (leterize d j book ctx typ) as)
  Era         -> Era
  Sup l a b   -> Sup (leterize d j book ctx typ l) (leterize d j book ctx typ a) (leterize d j book ctx typ b)
  SupM l f    -> SupM (leterize d j book ctx typ l) (leterize d j book ctx typ f)
  Loc s t'    -> Loc s (leterize d j book ctx typ t')
  Log s x     -> Log (leterize d j book ctx typ s) (leterize d j book ctx typ x)
  Pri p       -> Pri p
  Pat ss ms cs -> Pat (map (leterize d j book ctx typ) ss) 
                      [(k, leterize d j book ctx typ v) | (k, v) <- ms]
                      [(map (leterize d j book ctx typ) ps, leterize d j book ctx typ rhs) | (ps, rhs) <- cs]
  Frk l a b   -> Frk (leterize d j book ctx typ l) (leterize d j book ctx typ a) (leterize d j book ctx typ b)

isLamMatch :: Term -> Bool
isLamMatch EmpM      = True
isLamMatch UniM{}    = True
isLamMatch BitM{}    = True
isLamMatch NatM{}    = True
isLamMatch LstM{}    = True
isLamMatch EnuM{}    = True
isLamMatch SigM{}    = True
isLamMatch SupM{}    = True
isLamMatch EqlM{}    = True
isLamMatch _         = False
