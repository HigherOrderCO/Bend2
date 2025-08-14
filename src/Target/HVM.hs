{-./../Core/Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Target.HVM where

import Control.Monad (forM)
import Core.Type
import Data.Either (partitionEithers)
import Data.List (unsnoc, sortBy)
import Data.Maybe (fromJust)
import Debug.Trace
import qualified Data.Map as M
import qualified Data.Set as S
import qualified HVM.Type as HVM

compile :: Book -> String
compile book@(Book defs _) =
  -- TODO: Error handling
  if M.notMember "main" defs then
    error "No main function found"
  else
    let ds      = map (compileDef book) (M.toList defs)
        (ts,fs) = partitionEithers ds
        main    = "@main = " ++ showHVM 1 (termToHVM book (Ref "main" 1)) ++ "\n\n"
    in prelude ++ main ++ unlines ts ++ unlines fs

prelude :: String
prelude = unlines [
    "// Prelude",
    "data List { #Nil #Cons{head tail} }",
    "data Nat { #Z #S{n} }",
    "@fix(&f) = (f @fix(f))",
    "@CHAR_TO_U64(x) = (+ x 0)",
    "@U64_TO_CHAR(x) = (+ (& x 0xFFFFFFFF) '\\0')",
    "@HVM_INC(x) = ↑x",
    "@HVM_DEC(x) = ↓x",
    "",
    "// Bend to HVM Compiler Output"
  ]

-- Compile a Bend function to an HVM definition
compileDef :: Book -> (Name, Defn) -> Either String String
compileDef book (nam, (_, tm, ty)) = case extractTypeDef tm of
  Just (_, ctrs) -> Left (compileType nam ctrs ++ "\n" ++ compileFn book nam tm ty)
  Nothing        -> Right (compileFn book nam tm ty)

compileType :: Name -> [(Name, [Name])] -> String
compileType nam ctrs =
  "data " ++ (defNam nam) ++ " {\n" ++ unlines (map (\c -> "  "++ compileCtr c) ctrs) ++ "}"
  where
    compileCtr (nam, fds) = "#" ++ (defNam nam) ++ "{" ++ unwords fds ++ "}"

compileFn :: Book -> Name -> Term -> Term -> String
compileFn book nam tm ty =
  "!@" ++ (defNam nam) ++ "(" ++ unwords argsStr ++ ") =\n  " ++ showHVM 1 bodHVM ++ "\n"
  where
    (eras,args,body) = collectLamArgs tm ty [] []
    argsStr          = map (\(k,ty) -> if isStri k ty then "!&"++k else "&"++k) args
    bodHVM           = foldr (\era x -> rewriteHVM (HVM.Var era) HVM.Era x) (termToHVM book body) eras
    isStri k ty      = alwaysMat k body || isNum ty
    isNum ty         = case ty of { Num _ -> True; _ -> False } -- We don't necessarily want to always do this, but most times it guarantees fast u32 duplication at no extra cost.
    alwaysMat x bod  = case cut bod of
      -- Matches this var
      App (BitM _ _) (cut -> Var y _)  | x == y -> True
      App (NatM _ _) (cut -> Var y _)  | x == y -> True
      App (LstM _ _) (cut -> Var y _)  | x == y -> True
      App (SigM _) (cut -> Var y _)    | x == y -> True
      Pat [(cut -> Var y _)] _ _ | x == y -> True
      -- All branches of the mat eventually match this var
      BitM f t                                                -> alwaysMat x f && alwaysMat x t
      NatM z (Lam p _ (subst p -> s))                        -> alwaysMat x z && alwaysMat x s
      LstM n (Lam h _ (subst h -> Lam t _ (subst t -> c)))   -> alwaysMat x n && alwaysMat x c
      SigM (Lam l _ (subst l -> (Lam r _ (subst r -> f))))   -> alwaysMat x f
      Pat _ _ c                                              -> all (\(p,f) -> alwaysMat x f) c
      -- Pass through terms that just bind
      Let k t v f                                            -> alwaysMat x (f (Var k 0))
      Use k v f                                              -> alwaysMat x (f v)
      SupM _ (Lam a _ (subst a -> Lam b _ (subst b -> f))) -> alwaysMat x f
      _ -> False

-- Extract constructor definition info from type definitions
extractTypeDef :: Term -> Maybe ([Name], [(Name, [Name])])
extractTypeDef tm = do
  (args, tmSig) <- getTypeArgs tm []
  css <- getTypeCss tmSig
  return (args, css)
  where
    getTypeArgs :: Term -> [Name] -> Maybe ([Name], Term)
    getTypeArgs (Lam arg _ tm) args = getTypeArgs (tm (Var arg 0)) (args ++ [arg])
    getTypeArgs tm             args = Just (args, tm)

    getTypeCss :: Term -> Maybe [(Name, [Name])]
    getTypeCss (Sig (Enu _) (Lam "ctr" _ (subst "ctr" -> Pat [(Var "ctr" _)] [] cs))) =
      forM cs (\(p, bod) -> do
        ctr <- case p of
          [Sym ctr] -> Just ctr
          _         -> Nothing
        fds <- getTypeCsFds bod
        return (ctr, fds))
    getTypeCss _ = Nothing

    getTypeCsFds :: Term -> Maybe [Name]
    getTypeCsFds (Sig _ (Lam fd _ (subst fd -> tm))) = do
      fds <- getTypeCsFds tm
      return $ fd : fds
    getTypeCsFds Uni = Just []
    getTypeCsFds _   = Nothing

termToHVM :: Book -> Term -> HVM.Core
termToHVM book term = go term where
  go (Var n _)     = HVM.Var n
  go (Ref k i)     = fromJust (refAppToHVM book (Ref k i))
  go (Sub t)       = termToHVM book t
  go (Fix n f)     = HVM.Ref "fix" 0 [HVM.Lam (bindNam n) (termToHVM book (f (Var n 0)))]
  go (Let k t v f) = HVM.Let HVM.LAZY (bindNam k) (termToHVM book v) (termToHVM book (f (Var k 0)))
  go (Use k v f)   = termToHVM book (f v)  -- Inline directly, no binding
  go Set           = HVM.Era
  go (Chk v t)     = termToHVM book v
  go Emp           = HVM.Era
  go EmpM          = HVM.Lam "x$" HVM.Era
  go Uni           = HVM.Era
  go One           = HVM.U32 1
  go (UniM f)      = HVM.Lam "x$" $ HVM.Mat HVM.SWI (HVM.Var "x$") [] [("1", [], termToHVM book f), ("_", [], HVM.App (termToHVM book $ UniM f) (HVM.Var "x$"))]
  go Bit           = HVM.Era
  go Bt0           = HVM.U32 0
  go Bt1           = HVM.U32 1
  go (BitM f t)    = HVM.Lam "x$" $ HVM.Mat HVM.SWI (HVM.Var "x$") [] [("0", [], termToHVM book f), ("_", [], termToHVM book t)]
  go Nat           = HVM.Era
  go Zer           = HVM.Ctr "#Z" []
  go (Suc p)       = HVM.Ctr "#S" [termToHVM book p]
  go (NatM z s)    = HVM.Lam "x$" $ HVM.Mat (HVM.MAT 0) (HVM.Var "x$") [] [("#Z", [], termToHVM book z), ("#S", ["x$p"], HVM.App (termToHVM book s) (HVM.Var "x$p"))]
  go (Lst t)       = HVM.Era
  go Nil           = HVM.Ctr "#Nil" []
  go (Con h t)     = HVM.Ctr "#Cons" [termToHVM book h, termToHVM book t]
  go (LstM n c)    = HVM.Lam "x$" $ HVM.Mat (HVM.MAT 0) (HVM.Var "x$") [] [("#Nil", [], termToHVM book n), ("#Cons", ["x$h", "x$t"], HVM.App (HVM.App (termToHVM book c) (HVM.Var "x$h")) (HVM.Var "x$t"))]
  go (Enu s)       = HVM.Era
  go (Sym s)       = error "TODO: termToHVM Sym"
  go (EnuM c e)    = error "TODO: termToHVM EnuM"
  go (Log s x)     = termToHVM book x  -- For HVM, just return the result expression
  go (Num _)       = HVM.Era
  go (Val v)       = valToHVM book v
  go (Op2 o a b)   = op2ToHVM book o a b
  go (Op1 o a)     = op1ToHVM book o a
  go (Sig _ _)     = HVM.Era
  go (Tup x y)     =
    case ctrToHVM book x y of
      Just hvm -> hvm
      Nothing -> HVM.Sup 0 (termToHVM book x) (termToHVM book y)
  go (SigM f)   =
    case f of
      (Lam l _ (subst l -> (Lam r _ (subst r -> f)))) ->
        HVM.Lam "x$" (HVM.Dup 0 l r (HVM.Var "x$") (termToHVM book f))
      _ ->
        HVM.Lam "x$" (HVM.Dup 0 "x$l" "x$r" (HVM.Var "x$") (HVM.App (HVM.App (termToHVM book f) (HVM.Var "x$l")) (HVM.Var "x$r")))
  go (All _ _)    = HVM.Era
  go (Lam n _ f)  = HVM.Lam (bindNam n) (termToHVM book (f (Var n 0)))
  -- Directly compile application of a boolean match to a scrutinee
  -- Avoids emitting (λx$ ~ x$ {..} x)
  go (App (BitM f t) x) =
    HVM.Mat HVM.SWI (termToHVM book x) [] [("0", [], termToHVM book f), ("_", [], termToHVM book t)]
  -- Directly compile application of a nat match to a scrutinee
  go (App (NatM z s) x) =
    HVM.Mat (HVM.MAT 0) (termToHVM book x) [] [("#Z", [], termToHVM book z), ("#S", ["x$p"], HVM.App (termToHVM book s) (HVM.Var "x$p"))]
  -- Directly compile application of a list match to a scrutinee
  go (App (LstM n c) x) =
    HVM.Mat (HVM.MAT 0) (termToHVM book x) [] [("#Nil", [], termToHVM book n), ("#Cons", ["x$h", "x$t"], HVM.App (HVM.App (termToHVM book c) (HVM.Var "x$h")) (HVM.Var "x$t"))]
  -- Directly compile application of a pair match to a scrutinee
  go (App (SigM f) x) =
    case f of
      (Lam l _ (subst l -> (Lam r _ (subst r -> bod)))) ->
        HVM.Dup 0 (bindNam l) (bindNam r) (termToHVM book x) (termToHVM book bod)
      _ ->
        HVM.Dup 0 "x$l" "x$r" (termToHVM book x) (HVM.App (HVM.App (termToHVM book f) (HVM.Var "x$l")) (HVM.Var "x$r"))
  -- Empty match applied: ignores scrutinee, erases
  go (App EmpM _) = HVM.Era
  -- Unit match applied: single branch, ignore scrutinee
  go (App (UniM f) _) = termToHVM book f
  -- Equality match applied: erased, single branch
  go (App (EqlM f) _) = termToHVM book f
  -- Special-case: applying a SupM to a scrutinee should compile to a direct DUP
  go (App (SupM l f) x) =
    case f of
      (Lam a _ (subst a -> Lam b _ (subst b -> bod))) ->
        HVM.Ref "DUP" 0 [ termToHVM book l
                        , termToHVM book x
                        , HVM.Lam (bindNam a) (HVM.Lam (bindNam b) (termToHVM book bod))
                        ]
      _ ->
        HVM.Ref "DUP" 0 [ termToHVM book l
                        , termToHVM book x
                        , HVM.Lam "x$l" (HVM.Lam "x$r" (HVM.App (HVM.App (termToHVM book f) (HVM.Var "x$l")) (HVM.Var "x$r")))
                        ]
  go (App f x)    =
    case refAppToHVM book term of
      Just hvm -> hvm
      Nothing -> HVM.App (termToHVM book f) (termToHVM book x)
  go (Eql _ _ _)  = HVM.Era
  go Rfl          = HVM.Era
  go (EqlM _)     = HVM.Era
  go (Met n t ts) = HVM.Era -- TODO: Met
  go Era          = HVM.Era
  go (Sup l a b)  =
    HVM.Let HVM.LAZY "sup0$" (termToHVM book a) $
    HVM.Let HVM.LAZY "sup1$" (termToHVM book b) $
    HVM.Ref "SUP" 0 [termToHVM book l, HVM.Var "sup0$", HVM.Var "sup1$"]
  go (SupM l f)   =
    -- Compile a superposition lambda-match by duplicating the scrutinee
    -- using the provided label, then evaluating the body with both sides.
    case f of
      (Lam a _ (subst a -> Lam b _ (subst b -> bod))) ->
        HVM.Lam "x$" $ HVM.Ref "DUP" 0 [ termToHVM book l
                                       , HVM.Var "x$"
                                       , HVM.Lam (bindNam a) (HVM.Lam (bindNam b) (termToHVM book bod))
                                       ]
      _ ->
        -- If fields aren't explicit, introduce them and apply the matcher.
        HVM.Lam "x$" $ HVM.Ref "DUP" 0 [ termToHVM book l
                                       , HVM.Var "x$"
                                       , HVM.Lam "x$l" (HVM.Lam "x$r" (HVM.App (HVM.App (termToHVM book f) (HVM.Var "x$l")) (HVM.Var "x$r")))
                                       ]
  go (Frk l a b)  = HVM.Era
  go (Rwt e f)    = HVM.Era  -- Erases at runtime
  go (Loc s t)    = termToHVM book t
  go (Pri p)      = fromJust (refAppToHVM book (Pri p))
  go (Pat x m c)  = patToHVM book x m c

ctrToHVM :: Book -> Term -> Term -> Maybe HVM.Core
ctrToHVM book x y = case (x, (unsnoc (flattenTup y))) of
  (Sym k, Just (xs, One)) -> Just (HVM.Ctr ('#':defNam k) (map (termToHVM book) xs))
  _ -> Nothing

valToHVM :: Book -> NVal -> HVM.Core
valToHVM book v = case v of
  U64_V v -> HVM.U32 (fromIntegral v)
  I64_V v -> HVM.Era
  F64_V v -> HVM.Era
  CHR_V c -> HVM.Chr c

op2ToHVM :: Book -> NOp2 -> Term -> Term -> HVM.Core
op2ToHVM book op a b = case op of
  ADD -> HVM.Op2 HVM.OP_ADD (termToHVM book a) (termToHVM book b)
  SUB -> HVM.Op2 HVM.OP_SUB (termToHVM book a) (termToHVM book b)
  MUL -> HVM.Op2 HVM.OP_MUL (termToHVM book a) (termToHVM book b)
  DIV -> HVM.Op2 HVM.OP_DIV (termToHVM book a) (termToHVM book b)
  MOD -> HVM.Op2 HVM.OP_MOD (termToHVM book a) (termToHVM book b)
  POW -> error "POW binary operator not yet supported on Bend-to-HVM compiler."
  EQL -> HVM.Op2 HVM.OP_EQ  (termToHVM book a) (termToHVM book b)
  NEQ -> HVM.Op2 HVM.OP_NE  (termToHVM book a) (termToHVM book b)
  LST -> HVM.Op2 HVM.OP_LT  (termToHVM book a) (termToHVM book b)
  GRT -> HVM.Op2 HVM.OP_GT  (termToHVM book a) (termToHVM book b)
  LEQ -> HVM.Op2 HVM.OP_LTE (termToHVM book a) (termToHVM book b)
  GEQ -> HVM.Op2 HVM.OP_GTE (termToHVM book a) (termToHVM book b)
  AND -> HVM.Op2 HVM.OP_AND (termToHVM book a) (termToHVM book b)
  OR  -> HVM.Op2 HVM.OP_OR  (termToHVM book a) (termToHVM book b)
  XOR -> HVM.Op2 HVM.OP_XOR (termToHVM book a) (termToHVM book b)
  SHL -> HVM.Op2 HVM.OP_LSH (termToHVM book a) (termToHVM book b)
  SHR -> HVM.Op2 HVM.OP_RSH (termToHVM book a) (termToHVM book b)

op1ToHVM :: Book -> NOp1 -> Term -> HVM.Core
op1ToHVM book op a = case op of
  NOT -> error "NOT unary operator not yet supported on Bend-to-HVM compiler."
  NEG -> error "NEG unary operator not yet supported on Bend-to-HVM compiler."

refAppToHVM :: Book -> Term -> Maybe HVM.Core
refAppToHVM book term =
  case collectApps term [] of
    (Ref k i, args) ->
      let (tm,ty)     = case getDefn book k of
            Just (_,tm,ty) -> (tm,ty)
            Nothing        -> error ("unknown ref in hvm backend: " ++ show k)
          (era,arg,_) = collectLamArgs tm ty [] []
          argsHVM     = map (termToHVM book) (drop (length era) args)
          ari         = length arg
          len         = length argsHVM
      in return $ wrapRef (defNam k) argsHVM len ari
    (Pri p, args) -> case p of
      U64_TO_CHAR -> return $ wrapRef "U64_TO_CHAR" (map (termToHVM book) args) (length args) 1
      CHAR_TO_U64 -> return $ wrapRef "CHAR_TO_U64" (map (termToHVM book) args) (length args) 1
      HVM_INC     -> return $ wrapRef "HVM_INC" (map (termToHVM book) args) (length args) 1
      HVM_DEC     -> return $ wrapRef "HVM_DEC" (map (termToHVM book) args) (length args) 1
    _ -> Nothing
  where
    -- Eta expand the Ref if less args than needed and rebuild the Apps if more args than needed
    wrapRef nam args len ari
      | len < ari =
        let var = "_a" ++ show len
            bod = wrapRef nam (args ++ [HVM.Var var]) (len+1) ari
        in HVM.Lam (bindNam var) bod
      | len == ari =
        HVM.Ref nam 0 args
      | len >  ari =
        let (refArgs, appArgs) = splitAt ari args
        in foldl HVM.App (HVM.Ref nam 0 refArgs) appArgs
      | otherwise = undefined

-- Convert a match (Pat) term to HVM
patToHVM :: Book -> [Term] -> [Move] -> [Case] -> HVM.Core
patToHVM book [x] m c@(([p], f) : _) =
  case p of
    (Var k i) -> HVM.Let HVM.LAZY (bindNam k) (termToHVM book x) (termToHVM book f) -- unreachable?
    (Emp)     -> HVM.Era
    (One)     -> termToHVM book f
    (Bt0)     -> bitMat
    (Bt1)     -> bitMat
    (Zer)     -> simpleMat
    (Suc _)   -> simpleMat
    (Nil)     -> simpleMat
    (Con _ _) -> simpleMat
    (Sym _)   -> error "Nested matches on constructors and matches on symbols are not yet supported on Bend-to-HVM compiler."
    (Tup (Var a _) (Var b _)) ->
      case ctrPatToHVM book x m c of
        Just hvm -> hvm
        Nothing  -> HVM.Dup 0 a b (termToHVM book x) (termToHVM book f)
    (Rfl)     -> termToHVM book (snd (head c))
    (Sup l (Var a _) (Var b _)) ->
      HVM.Ref "DUP" 0 [termToHVM book l, termToHVM book x, (HVM.Lam (bindNam a) (HVM.Lam (bindNam b) (termToHVM book f)))]
    _ -> HVM.Era
  where
    -- A match that is contained in a single Pat term (bool, nat, list, pair)
    simpleMat = HVM.Mat (HVM.MAT 0) (termToHVM book x) hvmMv sortedCs
    hvmMv     = map (\(k,v) -> (bindNam k, termToHVM book v)) m
    -- Bend can output first True (1/_) and then False (0), so need to sort.
    -- A coincidence, but lexicographic string order actually works for this (vars can't start with $ but HVM already requires that)
    sortedCs  = sortBy (\(a,_,_) (b,_,_) -> compare a b) hvmCs
    hvmCs     = map (\(p,x) -> case head p of
        (Bt0)                     -> ("0", [], termToHVM book x)
        (Bt1)                     -> ("_", [], termToHVM book x)
        (Zer)                     -> ("#Z", [], termToHVM book x)
        (Suc (Var k _))           -> ("#S", [bindNam k], termToHVM book x)
        (Nil)                     -> ("#Nil", [], termToHVM book x)
        (Con (Var h _) (Var t _)) -> ("#Cons", [bindNam h, bindNam t], termToHVM book x)
        (Var k _)                 -> (bindNam k, [], termToHVM book x)
        _                         -> ("_", [], HVM.Era)
      ) goodCs
    goodCs = filter (not . badPatCase) c
    bitMat = case c of
      (([Bt0],f):([Bt1],t):_) -> tm (termToHVM book f) (termToHVM book t)
      (([Bt1],t):([Bt0],f):_) -> tm (termToHVM book f) (termToHVM book t)
      (([Bt0],f):([Var k _],t):_) -> tm (termToHVM book f) (HVM.Let HVM.LAZY k (HVM.Op2 HVM.OP_ADD (HVM.U32 1) (HVM.Var "bp$")) (termToHVM book t))
      (([Bt1],f):([Var k _],t):_) -> tm (HVM.Let HVM.LAZY k (HVM.U32 0) (termToHVM book f)) (termToHVM book t)
      _ -> HVM.Era
      where tm f t = HVM.Mat HVM.SWI (termToHVM book x) hvmMv [("0", [], f), ("1+bp$", [], t)]
patToHVM book x m c = HVM.Era

-- Since ctrs are desugared to a Sym + some Tups, the nested matches on the fields happen before the Tup matches on the entire constructor.
-- We need to somehow reorder the cases so that first we match on the entire constructor and only then on the fields.
ctrPatToHVM :: Book -> Term -> [Move] -> [Case] -> Maybe HVM.Core
ctrPatToHVM book x m c = case c of
  (([Tup (Var a _) (Var kB _)], Pat [(Var k _)] _ c) : _) ->
    if a == k then do
      let mv = map (\(k,v) -> (bindNam k, termToHVM book v)) m
      cs <- mapM (\(p, x) -> case head p of
          Sym ctr  -> caseToHVM ctr [] x
          Var kT _ -> return (bindNam kT, [], rewriteDflt kT kB (termToHVM book x))
          _ -> Nothing
        ) (filter (not . badPatCase) c)
      return $ HVM.Mat (HVM.MAT 0) (termToHVM book x) mv cs
    else Nothing
  _ -> Nothing
  where
    caseToHVM :: Name -> [Name] -> Term ->  Maybe HVM.Case
    caseToHVM ctr fds (Pat [(Var k _)] _ (([(Tup (Var a _) (Var b _))], bod) : _)) = caseToHVM ctr (fds ++ [a]) bod
    caseToHVM ctr fds (Pat [(Var k _)] _ (([One], bod) : _)) = Just ('#':defNam ctr, map bindNam fds, termToHVM book bod)
    caseToHVM _ _ _ = Nothing

    rewriteDflt kT kB x = rewriteHVM (HVM.Sup 0 (HVM.Var kT) (HVM.Var kB)) (HVM.Var kT) x


-- Utils
--------

-- Flattener generates cases with empty Pats when they're unreachable
badPatCase :: Case -> Bool
badPatCase ([Var _ _], cut -> Pat _ _ []) = True
badPatCase _ = False

defNam :: Name -> HVM.Name
defNam n = (replace '/' "__" n) ++ "$"

bindNam :: Name -> HVM.Name
bindNam n = if n == "_" then "_" else ('&':n)

subst :: Name -> Body -> Term
subst a f = f (Var a 0)

replace :: Char -> String -> String -> String
replace old new xs = foldr (\c acc -> if c == old then new ++ acc else c : acc) [] xs

-- Separates a function's body and signature into:
-- A list of erased arguments (leading lambdas of type Set)
-- A list of non-matching runtime arguments (lambdas after those of type Set)
-- The remaining body after the lambdas
collectLamArgs :: Term -> Term -> [Name] -> [(Name, Term)] -> ([Name], [(Name, Term)], Term)
collectLamArgs tm ty argsEra argsBod = case (tm, ty) of
  (Lam xtm _ (subst xtm -> bod), All (cut -> xty) (Lam x _ (subst x -> ty))) ->
    case (xty, argsBod) of
      (Set, []) -> collectLamArgs bod ty (argsEra ++ [xtm]) argsBod
      _         -> collectLamArgs bod ty argsEra (argsBod ++ [(xtm, xty)])
  _ -> (argsEra, argsBod, tm)

-- Rewrite structurally identical HVM terms
rewriteHVM :: HVM.Core -> HVM.Core -> HVM.Core -> HVM.Core
rewriteHVM old new tm =
  if tm == old
    then new
    else case tm of
      HVM.Var n         -> HVM.Var n
      HVM.Ref n k xs    -> HVM.Ref n k (map (rewriteHVM old new) xs)
      HVM.Era           -> HVM.Era
      HVM.Lam n f       -> HVM.Lam n (rewriteHVM old new f)
      HVM.App f x       -> HVM.App (rewriteHVM old new f) (rewriteHVM old new x)
      HVM.Sup l a b     -> HVM.Sup l (rewriteHVM old new a) (rewriteHVM old new b)
      HVM.Dup l a b v x -> HVM.Dup l a b (rewriteHVM old new v) (rewriteHVM old new x)
      HVM.Ctr n xs      -> HVM.Ctr n (map (rewriteHVM old new) xs)
      HVM.U32 n         -> HVM.U32 n
      HVM.Chr c         -> HVM.Chr c
      HVM.Op2 o a b     -> HVM.Op2 o (rewriteHVM old new a) (rewriteHVM old new b)
      HVM.Let t n v f   -> HVM.Let t n (rewriteHVM old new v) (rewriteHVM old new f)
      HVM.Mat t x mv cs -> HVM.Mat t (rewriteHVM old new x) (map (\(n,v) -> (n,rewriteHVM old new v)) mv) (map (\(c,f,b) -> (c,f,rewriteHVM old new b)) cs)
      HVM.Inc a         -> HVM.Inc (rewriteHVM old new a)
      HVM.Dec a         -> HVM.Dec (rewriteHVM old new a)

-- Alternative HVM show function suitable for compiler output
showHVM :: Int -> HVM.Core -> String
showHVM lv tm =
  case pretty tm of
    Just s -> s
    Nothing -> go tm
  where
    indent lv = replicate (lv * 2) ' '
    go (HVM.Var k)         = k
    go (HVM.Ref k i xs)    = "@" ++ k ++ "(" ++ unwords (map (showHVM lv) xs) ++ ")"
    go HVM.Era             = "*"
    go (HVM.Lam x f)       = "λ" ++ x ++ " " ++ showHVM lv f
    go (HVM.App f x)       = "(" ++ showHVM lv f ++ " " ++ showHVM lv x ++ ")"
    go (HVM.Sup l a b)     = "&" ++ show l ++ "{" ++ showHVM lv a ++ " " ++ showHVM lv b ++ "}"
    go (HVM.Dup l x y v f) = "!&" ++ show l ++ "{" ++ x ++ " " ++ y ++ "} = " ++ showHVM lv v ++ "\n" ++ indent lv ++ showHVM lv f
    go (HVM.Ctr k [])      = k
    go (HVM.Ctr k xs)      = k ++ "{" ++ unwords (map (showHVM lv) xs) ++ "}"
    go (HVM.U32 v)         = show v
    go (HVM.Chr v)         = "'" ++ [v] ++ "'"
    go (HVM.Op2 o a b)     = "(" ++ show o ++ " " ++ showHVM lv a ++ " " ++ showHVM lv b ++ ")"
    go (HVM.Let m k v f)   =
      let rhs = showHVM (lv+1) v in
      if '\n' `elem` rhs
        then "! " ++ show m ++ k ++ " =\n" ++ indent (lv+1) ++ rhs ++ "\n" ++ indent lv ++ showHVM lv f
        else "! " ++ show m ++ k ++ " = " ++ rhs ++ "\n" ++ indent lv ++ showHVM lv f
    go (HVM.Mat k v m ks)  = "~ " ++ showHVM lv v ++ concatMap showMov m ++ " {\n" ++ unlines (map showCase ks) ++ indent lv ++ "}"
        where showMov (k,v)     = " !" ++ k ++ "=" ++ showHVM lv v
              showCase (c,[],b) = indent (lv+1) ++ c ++ ":\n" ++ indent (lv+2) ++ showHVM (lv+2) b
              showCase (c, f,b) = indent (lv+1) ++ c ++ "{" ++ unwords f ++ "}" ++ ":\n" ++ indent (lv+2) ++ showHVM (lv+2) b
    go (HVM.Inc x)         = "↑" ++ showHVM lv x
    go (HVM.Dec x)         = "↓" ++ showHVM lv x

    pretty tm
      | Just s <- prettyDup tm = Just s
      | Just s <- prettySup tm = Just s
      | Just s <- prettyStr tm [] = Just s
      | Just s <- prettyLst tm [] = Just s
      | otherwise = Nothing

    prettyDup (HVM.Ref "DUP" i [HVM.Var l, v, HVM.Lam x (HVM.Lam y f)]) =
      Just $ "!&" ++ l ++ "{" ++ x ++ " " ++ y ++ "} = " ++ showHVM lv v ++ "\n" ++ indent lv ++ showHVM lv f
    prettyDup (HVM.Ref "DUP" i [HVM.U32 l, v, HVM.Lam x (HVM.Lam y f)]) =
      Just $ "!&" ++ show l ++ "{" ++ x ++ " " ++ y ++ "} = " ++ showHVM lv v ++ "\n" ++ indent lv ++ showHVM lv f
    prettyDup _ = Nothing

    prettySup (HVM.Ref "SUP" i [HVM.Var l, a, b]) =
      Just $ "&" ++ l ++ "{" ++ showHVM lv a ++ " " ++ showHVM lv b ++ "}"
    prettySup (HVM.Ref "SUP" i [HVM.U32 l, a, b]) =
      Just $ "&" ++ show l ++ "{" ++ showHVM lv a ++ " " ++ showHVM lv b ++ "}"
    prettySup _ = Nothing

    prettyStr (HVM.Ctr "#Cons" [HVM.Chr h, t]) acc = prettyStr t (h : acc)
    prettyStr (HVM.Ctr "#Nil" [])              acc = Just $ "\"" ++ reverse acc ++ "\""
    prettyStr _ _ = Nothing

    prettyLst (HVM.Ctr "#Cons" [h, t]) acc = prettyLst t (showHVM lv h : acc)
    prettyLst (HVM.Ctr "#Nil" [])      acc = Just $ "[" ++ unwords (reverse acc) ++ "]"
    prettyLst _ _ = Nothing





