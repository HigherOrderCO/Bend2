{-./Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Equal where

import System.IO.Unsafe
import Data.IORef
import Data.Bits
import Data.Maybe (fromMaybe, isNothing)
import Control.Applicative
import GHC.Float (castDoubleToWord64, castWord64ToDouble)

import Core.Type
import Core.WHNF

import Debug.Trace

-- Equality
-- ========

equal :: Int -> Book -> Term -> Term -> Bool
equal d book a b =
  -- trace ("- equal: " ++ show (normal book a) ++ " == " ++ show (normal book b)) $
  eql True d book a b

eql :: Bool -> Int -> Book -> Term -> Term -> Bool
eql False d book a b = cmp False d book (cut a) (cut b)
eql True  d book a b = 
  if identical 
    then
      -- trace ("identic " ++ show a ++ " == " ++ show b) $
      True
    else if similar
      then 
        -- trace ("similar " ++ show a ++ " == " ++ show b) $
        -- trace ("similar " ++ show (force book a) ++ " ~~ " ++ show (force book b)) $
        True
      else False
  where
    identical = eql False d book a b
    similar   = cmp True  d book (force book a) (force book b)

cmp :: Bool -> Int -> Book -> Term -> Term -> Bool
cmp red d book a b =
  case (a , b) of
    (Fix ka fa      , Fix kb fb      ) -> eql red d book (fa (fb (Var ka d))) (fb (fa (Var kb d)))
    (Fix ka fa      , b              ) -> eql red d book (fa b) b
    (a              , Fix kb fb      ) -> eql red d book a (fb (Fix kb fb))
    (Ref ka ia      , Ref kb ib      ) -> ka == kb
    (Ref ka ia      , b              ) -> case getDefn book ka of { Just (_, term, _) -> eql red d book term b ; Nothing -> False }
    (a              , Ref kb ib      ) -> case getDefn book kb of { Just (_, term, _) -> eql red d book a term ; Nothing -> False }
    (Var ka ia      , Var kb ib      ) -> ia == ib
    (Sub ta         , Sub tb         ) -> eql red d book ta tb
    (Let ka ta va fa, Let kb tb vb fb) -> eql red d book va vb && eql red (d+1) book (fa (Var ka d)) (fb (Var kb d)) && fromMaybe True (liftA2 (eql red d book) ta tb)
    (Use ka va fa   , Use kb vb fb   ) -> eql red d book va vb && eql red d book (fa va) (fb vb)
    (Set            , Set            ) -> True
    (Chk xa ta      , Chk xb tb      ) -> eql red d book xa xb && eql red d book ta tb
    (Tst xa         , Tst xb         ) -> eql red d book xa xb
    (Emp            , Emp            ) -> True
    (EmpM           , EmpM           ) -> True
    (Uni            , Uni            ) -> True
    (One            , One            ) -> True
    (UniM fa        , UniM fb        ) -> eql red d book fa fb
    (Bit            , Bit            ) -> True
    (Bt0            , Bt0            ) -> True
    (Bt1            , Bt1            ) -> True
    (BitM fa ta     , BitM fb tb     ) -> eql red d book fa fb && eql red d book ta tb
    (Nat            , Nat            ) -> True
    (Zer            , Zer            ) -> True
    (Suc na         , Suc nb         ) -> eql red d book na nb
    (NatM za sa     , NatM zb sb     ) -> eql red d book za zb && eql red d book sa sb
    (Lst ta         , Lst tb         ) -> eql red d book ta tb
    (Nil            , Nil            ) -> True
    (Con ha ta      , Con hb tb      ) -> eql red d book ha hb && eql red d book ta tb
    (LstM na ca     , LstM nb cb     ) -> eql red d book na nb && eql red d book ca cb
    (Enu sa         , Enu sb         ) -> sa == sb
    (Sym sa         , Sym sb         ) -> sa == sb
    (EnuM ca da     , EnuM cb db     ) -> length ca == length cb && all (\ ((s1,t1), (s2,t2)) -> s1 == s2 && eql red d book t1 t2) (zip ca cb) && eql red d book da db
    (Sig aa ba      , Sig ab bb      ) -> eql red d book aa ab && eql red d book ba bb
    (Tup aa ba      , Tup ab bb      ) -> eql red d book aa ab && eql red d book ba bb
    (SigM fa        , SigM fb        ) -> eql red d book fa fb
    (All aa ba      , All ab bb      ) -> eql red d book aa ab && eql red d book ba bb
    (Lam ka ta fa   , Lam kb tb fb   ) -> eql red (d+1) book (fa (Var ka d)) (fb (Var kb d)) && fromMaybe True (liftA2 (eql red d book) ta tb)
    (App fa xa      , App fb xb      ) -> eql red d book fa fb && eql red d book xa xb
    (Eql ta aa ba   , Eql tb ab bb   ) -> eql red d book ta tb && eql red d book aa ab && eql red d book ba bb
    -- (Eql ta _  _  , b            ) -> eql red d book ta b
    -- (a            , Eql tb _  _  ) -> eql red d book a tb
    (Rfl            , Rfl            ) -> True
    (Rwt ea fa      , Rwt eb fb      ) -> eql red d book ea eb && eql red d book fa fb
    (Loc _ ta       , b              ) -> eql red d book ta b
    (a              , Loc _ tb       ) -> eql red d book a tb
    (Era            , Era            ) -> True
    (Sup la aa ba   , Sup lb ab bb   ) -> eql red d book la lb && eql red d book aa ab && eql red d book ba bb
    (SupM la fa     , SupM lb fb     ) -> eql red d book la lb && eql red d book fa fb
    (Frk la aa ba   , Frk lb ab bb   ) -> eql red d book la lb && eql red d book aa ab && eql red d book ba bb
    (Num ta         , Num tb         ) -> ta == tb
    (Val va         , Val vb         ) -> va == vb
    (Op2 oa aa ba   , Op2 ob ab bb   ) -> oa == ob && eql red d book aa ab && eql red d book ba bb
    (Op1 oa aa      , Op1 ob ab      ) -> oa == ob && eql red d book aa ab
    (Pri pa         , Pri pb         ) -> pa == pb
    (Met _  _  _    , Met _  _  _    ) -> error "not-supported"
    (Pat _  _  _    , Pat _  _  _    ) -> error "not-supported"
    (_              , _              ) -> False
