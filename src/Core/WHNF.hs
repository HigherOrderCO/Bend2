{-./Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.WHNF where

import Debug.Trace

import Core.Type

import System.IO.Unsafe
import Data.IORef
import Data.Bits
import GHC.Float (castDoubleToWord64, castWord64ToDouble)

-- Evaluation
-- ==========

-- Levels:
-- - 0: decorations
-- - 1: reduce applications, eliminators, operators and primitives
-- - 2: reduce Fixes and non-injective Refs in wnf position
-- - 3: reduce everything

-- Reduction
whnf :: Int -> Int -> Book -> Subs -> Term -> Term
whnf lv d book subs term
  | ugly nf   = term
  | otherwise = nf
  where nf = whnfGo lv d book subs term

whnfGo :: Int -> Int -> Book -> Subs -> Term -> Term
whnfGo 0 d book subs term =
  case term of
    Let v f -> whnfLet 0 d book subs v f
    Ann x _ -> whnf 0 d book subs x
    Chk x _ -> whnf 0 d book subs x
    Loc _ t -> whnf 0 d book subs t
    _       -> term
whnfGo lv d book subs term =
  case subst lv d book subs [] term of
    Just (s,t) -> whnf lv d book s t
    Nothing    -> 
      case term of
        Let v f    -> whnfLet lv d book subs v f
        Ref k      -> whnfRef lv d book subs k
        Fix k f    -> whnfFix lv d book subs k f
        Ann x _    -> whnf lv d book subs x
        Chk x _    -> whnf lv d book subs x
        App f x    -> whnfApp lv d book subs (App f x) f x
        Loc _ t    -> whnf lv d book subs t
        Op2 o a b  -> whnfOp2 lv d book subs o a b
        Op1 o a    -> whnfOp1 lv d book subs o a
        Pri p      -> Pri p
        UniM x f   -> whnfUniM lv d book subs term x f
        BitM x f t -> whnfBitM lv d book subs term x f t
        NatM x z s -> whnfNatM lv d book subs term x z s
        LstM x n c -> whnfLstM lv d book subs term x n c
        EnuM x c f -> whnfEnuM lv d book subs term x c f
        SigM x f   -> whnfSigM lv d book subs term x f
        EqlM x f   -> whnfEqlM lv d book subs term x f
        _          -> term

-- Normalizes a let binding
whnfLet :: Int -> Int -> Book -> Subs -> Term -> Term -> Term
whnfLet lv d book subs v f = whnf lv d book subs (App f v)

-- Normalizes a reference
whnfRef :: Int -> Int -> Book -> Subs -> Name -> Term
whnfRef lv d book subs k =
  case lv of
    0 -> Ref k
    1 -> Ref k
    2 -> case deref book k of
      Just (True , term, _) -> Ref k
      Just (False, term, _) -> whnf lv d book subs term
      Nothing               -> Ref k
    3 -> case deref book k of
      Just (_, term, _) -> whnf lv d book subs term
      Nothing           -> Ref k
    _ -> error "unreachable"

-- Normalizes a fixpoint
whnfFix :: Int -> Int -> Book -> Subs -> String -> Body -> Term
whnfFix lv d book subs k f =
  case lv of
    0 -> Fix k f
    1 -> Fix k f
    2 -> Fix k f
    3 -> whnf lv d book subs (f (Fix k f))
    _ -> error "unreachable"

-- Normalizes a reference in an application
whnfAppRef :: Int -> Int -> Book -> Subs -> Term -> Name -> Term -> Term
whnfAppRef 0  d _    subs undo k x = App (Ref k) x
whnfAppRef 1  d _    subs undo k x = App (Ref k) x
whnfAppRef 2  d book subs undo k x =
  case deref book k of
    Just (inj, term, _) | inj       -> App (Ref k) x
                        | otherwise -> whnfApp 1 d book subs undo term x
    Nothing -> App (Ref k) x
whnfAppRef lv d book subs undo k x =
  case deref book k of
    Just (_, term, _) -> whnfApp lv d book subs undo term x
    Nothing           -> undo

-- Normalizes an application
whnfApp :: Int -> Int -> Book -> Subs -> Term -> Term -> Term -> Term
whnfApp lv d book subs undo f x =
  case whnf lv d book subs f of
    Lam _ f'  -> whnfAppLam lv d book subs f' x
    Fix k f'  -> whnfAppFix lv d book subs undo k f' x
    Ref k     -> whnfAppRef lv d book subs undo k x
    Pri p     -> whnfAppPri lv d book subs undo p x
    Sup _ _ _ -> error "Sup interactions unsupported in Haskell"
    _         -> undo

-- Normalizes a lambda application
whnfAppLam :: Int -> Int -> Book -> Subs -> Body -> Term -> Term
whnfAppLam lv d book subs f x = whnf lv d book subs (f x)

-- Normalizes a fixpoint application
whnfAppFix :: Int -> Int -> Book -> Subs -> Term -> String -> Body -> Term -> Term
whnfAppFix 0  d book subs undo k f x = App (Fix k f) x
whnfAppFix 1  d book subs undo k f x = App (Fix k f) x
whnfAppFix lv d book subs undo k f x = whnfApp lv d book subs undo (f (Fix k f)) x

-- Eliminator normalizers
-- ----------------------

-- Normalizes a unit match
whnfUniM :: Int -> Int -> Book -> Subs -> Term -> Term -> Term -> Term
whnfUniM lv d book subs undo x f =
  case whnf lv d book subs x of
    One -> whnf lv d book subs f
    _   -> undo

-- Normalizes a boolean match
whnfBitM :: Int -> Int -> Book -> Subs -> Term -> Term -> Term -> Term -> Term
whnfBitM lv d book subs undo x f t =
  case whnf lv d book subs x of
    Bt0 -> whnf lv d book subs f
    Bt1 -> whnf lv d book subs t
    _   -> undo

-- Normalizes a natural number match
whnfNatM :: Int -> Int -> Book -> Subs -> Term -> Term -> Term -> Term -> Term
whnfNatM lv d book subs undo x z s =
  case whnf lv d book subs x of
    Zer   -> whnf lv d book subs z
    Suc n -> whnf lv d book subs (App s (whnf lv d book subs n))
    _     -> undo

-- Normalizes a list match
whnfLstM :: Int -> Int -> Book -> Subs -> Term -> Term -> Term -> Term -> Term
whnfLstM lv d book subs undo x n c =
  case whnf lv d book subs x of
    Nil     -> whnf lv d book subs n
    Con h t -> whnf lv d book subs (App (App c (whnf lv d book subs h)) (whnf lv d book subs t))
    _       -> undo

-- Normalizes a pair match
whnfSigM :: Int -> Int -> Book -> Subs -> Term -> Term -> Term -> Term
whnfSigM lv d book subs undo x f =
  case whnf lv d book subs x of
    Tup a b -> whnf lv d book subs (App (App f (whnf lv d book subs a)) (whnf lv d book subs b))
    _       -> undo

-- Normalizes an enum match
whnfEnuM :: Int -> Int -> Book -> Subs -> Term -> Term -> [(String,Term)] -> Term -> Term
whnfEnuM lv d book subs undo x c f =
  case whnf lv d book subs x of
    Sym s -> case lookup s c of
      Just t  -> whnf lv d book subs t
      Nothing -> whnf lv d book subs (App f (Sym s))
    _         -> undo

-- Normalizes an equality match
whnfEqlM :: Int -> Int -> Book -> Subs -> Term -> Term -> Term -> Term
whnfEqlM lv d book subs undo x f =
  case whnf lv d book subs x of
    Rfl -> whnf lv d book subs f
    _   -> undo

-- Normalizes a primitive application
whnfAppPri :: Int -> Int -> Book -> Subs -> Term -> PriF -> Term -> Term
whnfAppPri lv d book subs undo U64_TO_CHAR x =
  case whnf lv d book subs x of
    Val (U64_V n) -> Val (CHR_V (toEnum (fromIntegral n)))
    _             -> undo

-- Numeric operations
-- ------------------

whnfOp2 :: Int -> Int -> Book -> Subs -> NOp2 -> Term -> Term -> Term
whnfOp2 lv d book subs op a b =
  case (whnf lv d book subs a, whnf lv d book subs b) of
    (Val (U64_V x), Val (U64_V y)) -> case op of
      ADD -> Val (U64_V (x + y))
      SUB -> Val (U64_V (x - y))
      MUL -> Val (U64_V (x * y))
      DIV -> if y == 0 then Op2 op (Val (U64_V x)) (Val (U64_V y)) else Val (U64_V (x `div` y))
      MOD -> if y == 0 then Op2 op (Val (U64_V x)) (Val (U64_V y)) else Val (U64_V (x `mod` y))
      EQL -> if x == y then Bt1 else Bt0
      NEQ -> if x /= y then Bt1 else Bt0
      LST -> if x < y then Bt1 else Bt0
      GRT -> if x > y then Bt1 else Bt0
      LEQ -> if x <= y then Bt1 else Bt0
      GEQ -> if x >= y then Bt1 else Bt0
      AND -> Val (U64_V (x .&. y))
      OR  -> Val (U64_V (x .|. y))
      XOR -> Val (U64_V (x `xor` y))
      SHL -> Val (U64_V (x `shiftL` fromIntegral y))
      SHR -> Val (U64_V (x `shiftR` fromIntegral y))
    (Val (I64_V x), Val (I64_V y)) -> case op of
      ADD -> Val (I64_V (x + y))
      SUB -> Val (I64_V (x - y))
      MUL -> Val (I64_V (x * y))
      DIV -> if y == 0 then Op2 op (Val (I64_V x)) (Val (I64_V y)) else Val (I64_V (x `div` y))
      MOD -> if y == 0 then Op2 op (Val (I64_V x)) (Val (I64_V y)) else Val (I64_V (x `mod` y))
      EQL -> if x == y then Bt1 else Bt0
      NEQ -> if x /= y then Bt1 else Bt0
      LST -> if x < y then Bt1 else Bt0
      GRT -> if x > y then Bt1 else Bt0
      LEQ -> if x <= y then Bt1 else Bt0
      GEQ -> if x >= y then Bt1 else Bt0
      -- Bitwise ops: convert I64 to U64 representation
      AND -> Val (U64_V (fromIntegral x .&. fromIntegral y))
      OR  -> Val (U64_V (fromIntegral x .|. fromIntegral y))
      XOR -> Val (U64_V (fromIntegral x `xor` fromIntegral y))
      SHL -> Val (U64_V (fromIntegral x `shiftL` fromIntegral y))
      SHR -> Val (U64_V (fromIntegral x `shiftR` fromIntegral y))
    (Val (F64_V x), Val (F64_V y)) -> case op of
      ADD -> Val (F64_V (x + y))
      SUB -> Val (F64_V (x - y))
      MUL -> Val (F64_V (x * y))
      DIV -> Val (F64_V (x / y))
      MOD -> Op2 op (Val (F64_V x)) (Val (F64_V y)) -- modulo not defined for floats
      EQL -> if x == y then Bt1 else Bt0
      NEQ -> if x /= y then Bt1 else Bt0
      LST -> if x < y then Bt1 else Bt0
      GRT -> if x > y then Bt1 else Bt0
      LEQ -> if x <= y then Bt1 else Bt0
      GEQ -> if x >= y then Bt1 else Bt0
      -- Bitwise ops: convert F64 to U64 bit representation
      AND -> Val (U64_V (castDoubleToWord64 x .&. castDoubleToWord64 y))
      OR  -> Val (U64_V (castDoubleToWord64 x .|. castDoubleToWord64 y))
      XOR -> Val (U64_V (castDoubleToWord64 x `xor` castDoubleToWord64 y))
      SHL -> Val (U64_V (castDoubleToWord64 x `shiftL` fromIntegral (castDoubleToWord64 y)))
      SHR -> Val (U64_V (castDoubleToWord64 x `shiftR` fromIntegral (castDoubleToWord64 y)))
    (Val (CHR_V x), Val (CHR_V y)) -> case op of
      ADD -> Val (CHR_V (toEnum (fromEnum x + fromEnum y)))
      SUB -> Val (CHR_V (toEnum (fromEnum x - fromEnum y)))
      MUL -> Val (CHR_V (toEnum (fromEnum x * fromEnum y)))
      DIV -> if fromEnum y == 0 then Op2 op (Val (CHR_V x)) (Val (CHR_V y)) else Val (CHR_V (toEnum (fromEnum x `div` fromEnum y)))
      MOD -> if fromEnum y == 0 then Op2 op (Val (CHR_V x)) (Val (CHR_V y)) else Val (CHR_V (toEnum (fromEnum x `mod` fromEnum y)))
      EQL -> if x == y then Bt1 else Bt0
      NEQ -> if x /= y then Bt1 else Bt0
      LST -> if x < y then Bt1 else Bt0
      GRT -> if x > y then Bt1 else Bt0
      LEQ -> if x <= y then Bt1 else Bt0
      GEQ -> if x >= y then Bt1 else Bt0
      -- Bitwise ops: convert CHR to U64 representation
      AND -> Op2 op (Val (CHR_V x)) (Val (CHR_V y)) -- bitwise not defined for chars
      OR  -> Op2 op (Val (CHR_V x)) (Val (CHR_V y)) -- bitwise not defined for chars
      XOR -> Op2 op (Val (CHR_V x)) (Val (CHR_V y)) -- bitwise not defined for chars
      SHL -> Op2 op (Val (CHR_V x)) (Val (CHR_V y)) -- bitwise not defined for chars
      SHR -> Op2 op (Val (CHR_V x)) (Val (CHR_V y)) -- bitwise not defined for chars
    (a', b') -> Op2 op a' b'

whnfOp1 :: Int -> Int -> Book -> Subs -> NOp1 -> Term -> Term
whnfOp1 lv d book subs op a =
  case whnf lv d book subs a of
    Val (U64_V x) -> case op of
      NOT -> Val (U64_V (complement x))
      NEG -> Op1 op (Val (U64_V x)) -- negation not defined for unsigned
    Val (I64_V x) -> case op of
      NOT -> Val (U64_V (complement (fromIntegral x))) -- convert to U64 for bitwise
      NEG -> Val (I64_V (-x))
    Val (F64_V x) -> case op of
      NOT -> Val (U64_V (complement (castDoubleToWord64 x))) -- convert to U64 for bitwise
      NEG -> Val (F64_V (-x))
    Val (CHR_V x) -> case op of
      NOT -> Op1 op (Val (CHR_V x)) -- bitwise not defined for chars
      NEG -> Op1 op (Val (CHR_V x)) -- negation not defined for chars
    a' -> Op1 op a'

-- Substitution
-- ============

subst :: Int -> Int -> Book -> Subs -> Subs -> Term -> Maybe (Subs, Term)
subst lv d book []           rems x = Nothing
subst 0  d book subs         rems x = Nothing
subst lv d book ((k,v):subs) rems x
  -- | eql lv d book [] k x = trace ("sub " ++ show (normal lv d book [] k) ++ " → " ++ show (normal lv d book [] v)) $ Just (rems ++ subs , v)
  -- | eql (case lv of { 3 -> 2 ; 2 -> 0 ; 1 -> 0 ; 0 -> 0 }) d book (rems++subs) k x = Just (rems ++ subs , v)
  | eql (down lv) d book (rems++subs) k x = Just (rems ++ subs , v)
  | otherwise                             = subst lv d book subs (rems ++ [(k,v)]) x

-- Equality
-- ========

eql :: Int -> Int -> Book -> Subs -> Term -> Term -> Bool
-- eql 0  d book subs a b = cmp 0 d book subs (whnf 0 book subs a) (whnf 0 book subs b)
eql 0  d book subs a b = cmp 0 d book subs a b
eql lv d book subs a b = identical || nf_equal where
  identical = eql 0 d book subs a b
  nf_equal  = cmp lv d book subs (whnf lv d book subs a) (whnf lv d book subs b)

cmp :: Int -> Int -> Book -> Subs -> Term -> Term -> Bool
cmp lv d book subs a b =
  -- trace ("E" ++ show lv ++ " " ++ show a ++ "\n== " ++ show b) $
  case (a , b) of
    (Fix ka fa     , Fix kb fb    ) -> eql lv d book subs (fa (fb (Var ka d))) (fb (fa (Var kb d)))
    (Fix ka fa     , b            ) -> eql lv d book subs (fa b) b
    (a             , Fix kb fb    ) -> eql lv d book subs a (fb (Fix kb fb))
    (Ref ka        , Ref kb       ) -> ka == kb
    (Ref ka        , b            ) -> case deref book ka of { Just (_, term, _) -> eql lv d book subs term b ; Nothing -> False }
    (a             , Ref kb       ) -> case deref book kb of { Just (_, term, _) -> eql lv d book subs a term ; Nothing -> False }
    (Var ka ia     , Var kb ib    ) -> ia == ib
    (Sub ta        , Sub tb       ) -> eql lv d book subs ta tb
    (Let va fa     , Let vb fb    ) -> eql lv d book subs va vb && eql lv d book subs fa fb
    (Set           , Set          ) -> True
    (Ann xa ta     , Ann xb tb    ) -> eql lv d book subs xa xb && eql lv d book subs ta tb
    (Chk xa ta     , Chk xb tb    ) -> eql lv d book subs xa xb && eql lv d book subs ta tb
    (Emp           , Emp          ) -> True
    (Efq           , Efq          ) -> True
    (Uni           , Uni          ) -> True
    (One           , One          ) -> True
    (UniM xa fa    , UniM xb fb   ) -> eql lv d book subs xa xb && eql lv d book subs fa fb
    (Bit           , Bit          ) -> True
    (Bt0           , Bt0          ) -> True
    (Bt1           , Bt1          ) -> True
    (BitM xa fa ta , BitM xb fb tb) -> eql lv d book subs xa xb && eql lv d book subs fa fb && eql lv d book subs ta tb
    (Nat           , Nat          ) -> True
    (Zer           , Zer          ) -> True
    (Suc na        , Suc nb       ) -> eql lv d book subs na nb
    (NatM xa za sa , NatM xb zb sb) -> eql lv d book subs xa xb && eql lv d book subs za zb && eql lv d book subs sa sb
    (Lst ta        , Lst tb       ) -> eql lv d book subs ta tb
    (Nil           , Nil          ) -> True
    (Con ha ta     , Con hb tb    ) -> eql lv d book subs ha hb && eql lv d book subs ta tb
    (LstM xa na ca , LstM xb nb cb) -> eql lv d book subs xa xb && eql lv d book subs na nb && eql lv d book subs ca cb
    (Enu sa        , Enu sb       ) -> sa == sb
    (Sym sa        , Sym sb       ) -> sa == sb
    (EnuM xa ca da , EnuM xb cb db) -> eql lv d book subs xa xb && length ca == length cb && all (\ ((s1,t1), (s2,t2)) -> s1 == s2 && eql lv d book subs t1 t2) (zip ca cb) && eql lv d book subs da db
    (Sig aa ba     , Sig ab bb    ) -> eql lv d book subs aa ab && eql lv d book subs ba bb
    (Tup aa ba     , Tup ab bb    ) -> eql lv d book subs aa ab && eql lv d book subs ba bb
    (SigM xa fa    , SigM xb fb   ) -> eql lv d book subs xa xb && eql lv d book subs fa fb
    (All aa ba     , All ab bb    ) -> eql lv d book subs aa ab && eql lv d book subs ba bb
    (Lam ka fa     , Lam kb fb    ) -> eql lv (d+1) book subs (fa (Var ka d)) (fb (Var kb d))
    (App fa xa     , App fb xb    ) -> eql lv d book subs fa fb && eql lv d book subs xa xb
    (Eql ta aa ba  , Eql tb ab bb ) -> eql lv d book subs ta tb && eql lv d book subs aa ab && eql lv d book subs ba bb
    (Rfl           , Rfl          ) -> True
    (EqlM xa fa    , EqlM xb fb   ) -> eql lv d book subs xa xb && eql lv d book subs fa fb
    (Ind ta        , b            ) -> eql lv d book subs ta b
    (a             , Ind tb       ) -> eql lv d book subs a tb
    (Frz ta        , b            ) -> eql lv d book subs ta b
    (a             , Frz tb       ) -> eql lv d book subs a tb
    (Loc _ ta      , b            ) -> eql lv d book subs ta b
    (a             , Loc _ tb     ) -> eql lv d book subs a tb
    (Rwt _ _ xa    , _            ) -> eql lv d book subs xa b
    (_             , Rwt _ _ xb   ) -> eql lv d book subs a xb
    (Era           , Era          ) -> True
    (Sup la aa ba  , Sup lb ab bb ) -> la == lb && eql lv d book subs aa ab && eql lv d book subs ba bb
    (Num ta        , Num tb       ) -> ta == tb
    (Val va        , Val vb       ) -> va == vb
    (Op2 oa aa ba  , Op2 ob ab bb ) -> oa == ob && eql lv d book subs aa ab && eql lv d book subs ba bb
    (Op1 oa aa     , Op1 ob ab    ) -> oa == ob && eql lv d book subs aa ab
    (Pri pa        , Pri pb       ) -> pa == pb
    (Met _  _  _   , Met _  _  _  ) -> error "not-supported"
    (Pat _  _  _   , Pat _  _  _  ) -> error "not-supported"
    (_             , _            ) -> False

-- Normalization
-- =============

normal :: Int -> Int -> Book -> Subs -> Term -> Term
normal lv d book subs term =
  -- trace ("normal: " ++ show lv ++ " " ++ show term) $
  case whnf lv d book subs term of
    Var k i    -> Var k i
    Ref k      -> Ref k
    Sub t      -> normal lv d book subs t
    Fix k f    -> Fix k (\x -> normal lv (d+1) book subs (f x))
    Let v f    -> Let (normal lv d book subs v) (normal lv d book subs f)
    Set        -> Set
    Ann x t    -> Ann (normal lv d book subs x) (normal lv d book subs t)
    Chk x t    -> Chk (normal lv d book subs x) (normal lv d book subs t)
    Emp        -> Emp
    Efq        -> Efq
    Uni        -> Uni
    One        -> One
    UniM x f   -> UniM (normal lv d book subs x) (normal lv d book subs f)
    Bit        -> Bit
    Bt0        -> Bt0
    Bt1        -> Bt1
    BitM x f t -> BitM (normal lv d book subs x) (normal lv d book subs f) (normal lv d book subs t)
    Nat        -> Nat
    Zer        -> Zer
    Suc n      -> Suc (normal lv d book subs n)
    NatM x z s -> NatM (normal lv d book subs x) (normal lv d book subs z) (normal lv d book subs s)
    Lst t      -> Lst (normal lv d book subs t)
    Nil        -> Nil
    Con h t    -> Con (normal lv d book subs h) (normal lv d book subs t)
    LstM x n c -> LstM (normal lv d book subs x) (normal lv d book subs n) (normal lv d book subs c)
    Enu s      -> Enu s
    Sym s      -> Sym s
    EnuM x c e -> EnuM (normal lv d book subs x) (map (\(s, t) -> (s, normal lv d book subs t)) c) (normal lv d book subs e)
    Sig a b    -> Sig (normal lv d book subs a) (normal lv d book subs b)
    Tup a b    -> Tup (normal lv d book subs a) (normal lv d book subs b)
    SigM x f   -> SigM (normal lv d book subs x) (normal lv d book subs f)
    All a b    -> All (normal lv d book subs a) (normal lv d book subs b)
    Lam k f    -> Lam k (\x -> normal 0 (d+1) book subs (f x)) -- note: uses lv=0 for finite pretty printing
    App f x    -> App (normal 1  d book subs f) (normal lv d book subs x)
    Eql t a b  -> Eql (normal lv d book subs t) (normal lv d book subs a) (normal lv d book subs b)
    Rfl        -> Rfl
    EqlM x f   -> EqlM (normal lv d book subs x) (normal lv d book subs f)
    Ind t      -> Ind (normal lv d book subs t)
    Frz t      -> Frz (normal lv d book subs t)
    Loc l t    -> Loc l (normal lv d book subs t)
    Rwt a b x  -> Rwt (normal lv d book subs a) (normal lv d book subs b) (normal lv d book subs x)
    Era        -> Era
    Sup l a b  -> Sup l (normal lv d book subs a) (normal lv d book subs b)
    Num t      -> Num t
    Val v      -> Val v
    Op2 o a b  -> Op2 o (normal lv d book subs a) (normal lv d book subs b)
    Op1 o a    -> Op1 o (normal lv d book subs a)
    Pri p      -> Pri p
    Met _ _ _  -> error "not-supported"
    Pat _ _ _  -> error "not-supported"

normalCtx :: Int -> Int -> Book -> Subs -> Ctx -> Ctx
normalCtx lv d book subs (Ctx ctx) = Ctx (map normalAnn ctx)
  where normalAnn (k,v,t) = (k, normal lv d book subs v, normal lv d book subs t)

-- Utils
-- =====

-- Shapes that are rolled back for pretty printing
ugly :: Term -> Bool
ugly (cut -> UniM _ _  ) = True
ugly (cut -> BitM _ _ _) = True
ugly (cut -> NatM _ _ _) = True
ugly (cut -> LstM _ _ _) = True
ugly (cut -> EnuM _ _ _) = True
ugly (cut -> SigM _ _  ) = True
ugly (cut -> EqlM _ _  ) = True
ugly _                   = False

-- Forces evaluation
force :: Int -> Book -> Subs -> Term -> Term
force d book subs t =
  case whnf 3 d book subs t of
    Ind t -> force d book subs t
    Frz t -> force d book subs t
    t     -> t

equal :: Int -> Book -> Subs -> Term -> Term -> Bool
equal d book subs a b =
  -- trace (""
    -- ++ "EQ: " ++ show (normal 3 d book []   a) ++ " == " ++ show (normal 3 d book []   b) ++ "\n"
    -- ++ "~>: " ++ show (normal 3 d book subs a) ++ " == " ++ show (normal 3 d book subs b)
    -- ++ concatMap (\ (a,b) -> "\n| " ++ show (normal 3 d book [] a) ++ " → " ++ show (normal 3 d book [] b)) subs) $
  eql 3 d book subs a b

normalize :: Int -> Book -> Subs -> Term -> Term
normalize = normal 3

normalizeCtx :: Int -> Book -> Subs -> Ctx -> Ctx
normalizeCtx = normalCtx 3

down :: Int -> Int
down 3 = 2
down 2 = 0
down 1 = 0
down 0 = 0
down n = n - 1
