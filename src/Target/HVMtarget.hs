{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}



module Target.HVMtarget where

import Control.Monad (forM)
import Core.Type
import Data.Int (Int64)
import Data.List (intercalate, isPrefixOf, isSuffixOf, isInfixOf)
import Data.Maybe (fromJust, fromMaybe)
import Data.Word (Word64)
import Debug.Trace
import qualified Control.Monad.State as ST
import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified Data.ByteString.Lazy.Char8 as BL

import Data.Text (pack, unpack, replace)


import qualified HVM.Type as HVM



prelude :: String
prelude = unlines [
  " // Translated from Bend",
  "data nat { #S{n} #Z}",
  "data list { #Nil #Cons{h t}}"
  ]

strToHVM :: String -> HVM.Core
strToHVM [] = HVM.Ctr "#Nil" []
strToHVM (c:cs) = HVM.Ctr "#Cons"  $ HVM.Chr c : [strToHVM cs]


toNative :: (M.Map String String) -> Term -> HVM.Core
toNative ctx tm = case tm of

  Var n i   ->
    case M.lookup n ctx of
      Just n -> HVM.Var $ "&" ++ n
      Nothing -> HVM.Var $ "&" ++ n
  Ref k      -> HVM.Var $ "@" ++ k
  Sub t      -> undefined
  Lam n f    -> HVM.Lam ('&':n) (toNative (M.insert n n ctx) (f (Var n 0)))
  App f x    -> HVM.App (toNative ctx f) (toNative ctx x)
  Let v f    -> HVM.App (toNative ctx f) (toNative ctx v)
  Fix n f    -> HVM.Ref "fix" 0 [HVM.Lam ('&':n) (toNative (M.insert n n ctx) (f (Var n 0)))]
  Chk v t    -> toNative ctx v
  EmpM x     -> HVM.Era
  One        -> HVM.U32 1
  UniM x f   -> toNative ctx f
  Bt0        -> HVM.Ctr "#B0" []
  Bt1        -> HVM.Ctr "#B1" []
  BitM x f t -> HVM.Mat (HVM.MAT 0) (toNative ctx x) [] [("#B0", [], toNative ctx f), ("#B1", [], toNative ctx t)]
  Zer        -> HVM.Ctr "#Z" []
  Suc p      -> HVM.Ctr "#S" [toNative ctx p]
  NatM x z s -> HVM.Mat (HVM.MAT 0) (toNative ctx x) [] [("#Z", [], toNative ctx z), ("#S", [], toNative ctx s)]
  Nil        -> HVM.Ctr "#Nil" []
  Con h t    -> HVM.Ctr "#Cons" [toNative ctx h, toNative ctx t]
  LstM x n c -> HVM.Mat (HVM.MAT 0) (toNative ctx x) [] [("#Nil", [], toNative ctx n), ("#Cons", [], toNative ctx c)]
  Sym s      -> strToHVM s
  EnuM x c e -> enumToNative ctx (toNative ctx x) c e
  Val (U64_V v) -> HVM.U32 (fromIntegral v)
  Val (I64_V v) -> error "TODO: toNative I64_V"
  Val (F64_V v) -> error "TODO: toNative F64_V"
  Val (CHR_V c) -> error "TODO: toNative CHR_V"
  Op2 o a b  -> op2ToNative o a b
  Op1 o a    -> op1ToNative o a
  Tup x y    -> HVM.Ctr "#P" [toNative ctx x, toNative ctx y]
  SigM x f   -> HVM.Mat (HVM.MAT 0) (toNative ctx x) [] [("#P", [], toNative ctx f)]
  Rfl        -> HVM.U32 0
  EqlM x f   -> toNative ctx f
  Ind t      -> toNative ctx t
  Frz t      -> toNative ctx t
  Loc s t    -> toNative ctx t
  Era        -> HVM.Era
  Sup l a b  -> HVM.Sup (fromIntegral l) (toNative ctx a) (toNative ctx b)
  Rwt a b x  -> HVM.Ctr "#RWT" [toNative ctx a, toNative ctx b, toNative ctx x]
  Pri p      -> undefined
  Met k t xs -> undefined
  Pat x m c  -> undefined
  _          -> HVM.Era

  where
    -- if x == y then f else (enumToNative ctx x t d)
    enumToNative ctx x ((y,f):t) d = HVM.Mat HVM.SWI (HVM.Ref "str_equal" 0 [x, strToHVM y]) [] [("0", [], enumToNative ctx x t d), ("_", [], toNative ctx f)]
    enumToNative ctx x []        d = toNative ctx d

    op2ToNative ADD a b = HVM.Op2 HVM.OP_ADD (toNative ctx a) (toNative ctx b)
    op2ToNative SUB a b = HVM.Op2 HVM.OP_SUB (toNative ctx a) (toNative ctx b)
    op2ToNative MUL a b = HVM.Op2 HVM.OP_MUL (toNative ctx a) (toNative ctx b)
    op2ToNative DIV a b = HVM.Op2 HVM.OP_DIV (toNative ctx a) (toNative ctx b)
    op2ToNative MOD a b = HVM.Op2 HVM.OP_MOD (toNative ctx a) (toNative ctx b)
    op2ToNative POW a b = error "TODO"
    op2ToNative EQL a b = HVM.Op2 HVM.OP_EQ  (toNative ctx a) (toNative ctx b)
    op2ToNative NEQ a b = HVM.Op2 HVM.OP_NE  (toNative ctx a) (toNative ctx b)
    op2ToNative LST a b = HVM.Op2 HVM.OP_LT  (toNative ctx a) (toNative ctx b)
    op2ToNative GRT a b = HVM.Op2 HVM.OP_GT  (toNative ctx a) (toNative ctx b)
    op2ToNative LEQ a b = HVM.Op2 HVM.OP_LTE (toNative ctx a) (toNative ctx b)
    op2ToNative GEQ a b = HVM.Op2 HVM.OP_GTE (toNative ctx a) (toNative ctx b)
    op2ToNative AND a b = HVM.Op2 HVM.OP_AND (toNative ctx a) (toNative ctx b)
    op2ToNative OR  a b = HVM.Op2 HVM.OP_OR  (toNative ctx a) (toNative ctx b)
    op2ToNative XOR a b = HVM.Op2 HVM.OP_XOR (toNative ctx a) (toNative ctx b)
    op2ToNative SHL a b = HVM.Op2 HVM.OP_LSH (toNative ctx a) (toNative ctx b)
    op2ToNative SHR a b = HVM.Op2 HVM.OP_RSH (toNative ctx a) (toNative ctx b)

    op1ToNative NOT = error "TODO"
    op1ToNative NEG = error "TODO"






-- linearize :: HVM.Core -> (HVM.Core, [Name])
-- linearize hvm =
--   case hvm of
--     HVM.Var n -> (hvm, [n])

--     HVM.Lam n t ->
--       (HVM.Lam n t, xs)
--       where
--         (t, xs) = linearize t

--     _         -> (hvm, [])



compileTerm :: Term -> String
compileTerm tm =

  let
    hvm = toNative M.empty tm
  in HVM.showCore hvm




-- -- Compile book to HVM
compile :: Book -> String
compile (Book defs) =

  -- let ctDefs = map (\(name, (_, term, _)) -> (name, termToCT (Book defs) term 0)) (M.toList defs)
  --     ctBook = M.fromList ctDefs
  --     jsFns = concatMap (generateJS ctBook) ctDefs
  -- in prelude ++ jsFns
  -- "[done]"
  -- compileTerm $ M.keys defs

  let
    hvmFns = map (\(name, (_inf, term, _typ)) -> "\n // " ++(show term) ++ "\n@" ++ name ++ " = " ++ compileTerm term) (M.toList defs)

  in prelude ++ unlines hvmFns



