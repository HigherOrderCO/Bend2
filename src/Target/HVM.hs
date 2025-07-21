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
import qualified Data.Map.Strict as MS
import qualified Data.Set as S
import qualified HVM.Type as HVM

compile :: Book -> String
compile book@(Book defs) =
  -- TODO: Error handling
  if M.notMember "main" defs then
    error "No main function found"
  else
    let ds      = map (compileDef book) (M.toList defs)
        (ts,fs) = partitionEithers ds
        main    = "@main = " ++ showHVM 1 (termToHVM book MS.empty (Ref "main")) ++ "\n\n"
    in prelude ++ main ++ unlines ts ++ unlines fs

prelude :: String
prelude = unlines [
    "// Prelude",
    "data List { #Nil #Cons{head tail} }",
    "data Nat { #Z #S{n} }",
    "data Pair { #P{fst snd} }",
    "@fix(&f) = (f @fix(f))",
    "@CHAR_TO_U64(x) = (+ x 0)",
    "@U64_TO_CHAR(x) = (+ (& x 0xFFFFFFFF) '\\0')",
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
    bodHVM           = foldr (\era x -> rewriteHVM (HVM.Var era) HVM.Era x) (termToHVM book MS.empty body) eras
    isStri k ty      = alwaysMat k body || isNum ty
    isNum ty         = case ty of { Num _ -> True; _ -> False } -- We don't necessarily want to always do this, but most times it guarantees fast u32 duplication at no extra cost.
    alwaysMat x bod  = case cut bod of
      -- Matches this var
      BitM (cut -> Var y _) _ _  | x == y -> True
      NatM (cut -> Var y _) _ _  | x == y -> True
      LstM (cut -> Var y _) _ _  | x == y -> True
      SigM (cut -> Var y _) _    | x == y -> True
      Pat [(cut -> Var y _)] _ _ | x == y -> True
      -- All branches of the mat eventually match this var
      BitM _ f t                                             -> alwaysMat x f && alwaysMat x t
      NatM _ z (Lam p _ (subst p -> s))                      -> alwaysMat x z && alwaysMat x s
      LstM _ n (Lam h _ (subst h -> Lam t _ (subst t -> c))) -> alwaysMat x n && alwaysMat x c
      SigM _ (Lam l _ (subst l -> (Lam r _ (subst r -> f)))) -> alwaysMat x f
      Pat _ _ c                                              -> all (\(p,f) -> alwaysMat x f) c
      -- Pass through terms that just bind
      Let k t v f                                            -> alwaysMat x (f (Var k 0))
      SupM _ _ (Lam a _ (subst a -> Lam b _ (subst b -> f))) -> alwaysMat x f
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

termToHVM :: Book -> MS.Map Name HVM.Name -> Term -> HVM.Core
termToHVM book ctx term = go term where
  go (Var n i) =
    case MS.lookup n ctx of
      Just n  -> HVM.Var n
      Nothing -> HVM.Var n
  go (Ref k)       = fromJust (refAppToHVM book ctx (Ref k))
  go (Sub t)       = termToHVM book ctx t
  go (Fix n f)     = HVM.Ref "fix" 0 [HVM.Lam (bindNam n) (termToHVM book (MS.insert n n ctx) (f (Var n 0)))]
  go (Let k t v f) = HVM.Let HVM.LAZY (bindNam k) (termToHVM book ctx v) (termToHVM book (MS.insert k k ctx) (f (Var k 0)))
  go Set          = HVM.Era
  go (Chk v t)    = termToHVM book ctx v
  go Emp          = HVM.Era
  go (EmpM x)     = HVM.Era
  go Uni          = HVM.Era
  go One          = HVM.U32 1
  go (UniM x f)   = termToHVM book ctx f
  go Bit          = HVM.Era
  go Bt0          = HVM.U32 0
  go Bt1          = HVM.U32 1
  go (BitM x f t) = HVM.Mat HVM.SWI (termToHVM book ctx x) [] [("0", [], termToHVM book ctx f), ("_", [], termToHVM book ctx t)]
  go Nat          = HVM.Era
  go Zer          = HVM.Ctr "#Z" []
  go (Suc p)      = HVM.Ctr "#S" [termToHVM book ctx p]
  go (NatM x z s) =
    case s of
      (Lam n _ (subst n -> s)) ->
        HVM.Mat (HVM.MAT 0) (termToHVM book ctx x) [] [("#Z", [], termToHVM book ctx z), ("#S", [n], termToHVM book ctx s)]
      _ ->
        HVM.Mat (HVM.MAT 0) (termToHVM book ctx x) [] [("#Z", [], termToHVM book ctx z), ("#S", ["x$p"], HVM.App (termToHVM book ctx s) (HVM.Var "x$p"))]
  go (Lst t)      = HVM.Era
  go Nil          = HVM.Ctr "#Nil" []
  go (Con h t)    = HVM.Ctr "#Cons" [termToHVM book ctx h, termToHVM book ctx t]
  go (LstM x n c) =
    case c of
      (Lam h _ (subst h -> (Lam t _ (subst t -> c)))) ->
        HVM.Mat (HVM.MAT 0) (termToHVM book ctx x) [] [("#Nil", [], termToHVM book ctx n), ("#Cons", [h, t], termToHVM book ctx c)]
      _ ->
        HVM.Mat (HVM.MAT 0) (termToHVM book ctx x) [] [("#Nil", [], termToHVM book ctx n), ("#Cons", ["x$h", "x$t"], HVM.App (HVM.App (termToHVM book ctx c) (HVM.Var "x$h")) (HVM.Var "x$t"))]
  go (Enu s)      = HVM.Era
  go (Sym s)      = error "TODO: termToHVM Sym"
  go (EnuM x c e) = error "TODO: termToHVM EnuM"
  go (Log s x)    = termToHVM book ctx x  -- For HVM, just return the result expression
  go (Num _)      = HVM.Era
  go (Val v)      = valToHVM book ctx v
  go (Op2 o a b)  = op2ToHVM book ctx o a b
  go (Op1 o a)    = op1ToHVM book ctx o a
  go (Sig _ _)    = HVM.Era
  go (Tup x y)    =
    case ctrToHVM book ctx x y of
      Just hvm -> hvm
      Nothing -> HVM.Ctr "#P" [termToHVM book ctx x, termToHVM book ctx y]
  go (SigM x f)   =
    case f of
      (Lam l _ (subst l -> (Lam r _ (subst r -> f)))) ->
        HVM.Mat (HVM.MAT 0) (termToHVM book ctx x) [] [("#P", [l, r], termToHVM book ctx f)]
      _ ->
        HVM.Mat (HVM.MAT 0) (termToHVM book ctx x) [] [("#P", ["x$l", "x$r"], HVM.App (HVM.App (termToHVM book ctx f) (HVM.Var "x$l")) (HVM.Var "x$r"))]
  go (All _ _)    = HVM.Era
  go (Lam n _ f)  = HVM.Lam (bindNam n) (termToHVM book (MS.insert n n ctx) (f (Var n 0)))
  go (App f x)    =
    case refAppToHVM book ctx term of
      Just hvm -> hvm
      Nothing -> HVM.App (termToHVM book ctx f) (termToHVM book ctx x)
  go (Eql _ _ _)  = HVM.Era
  go Rfl          = HVM.Era
  go (EqlM x f)   = termToHVM book ctx f
  go (Met n t ts) = HVM.Era -- TODO: Met
  go (Ind t)      = termToHVM book ctx t
  go (Frz t)      = termToHVM book ctx t
  go Era          = HVM.Era
  go (Sup l a b)  =
    HVM.Let HVM.LAZY "sup0$" (termToHVM book ctx a) $
    HVM.Let HVM.LAZY "sup1$" (termToHVM book ctx b) $
    HVM.Ref "SUP" 0 [termToHVM book ctx l, HVM.Var "sup0$", HVM.Var "sup1$"]
  go (SupM x l f) = HVM.Ref "DUP" 0 [termToHVM book ctx l, termToHVM book ctx x, termToHVM book ctx f]
  go (Frk l a b)  = HVM.Era
  go (Loc s t)    = termToHVM book ctx t
  go (Rwt _ _ x)  = termToHVM book ctx x
  go (Pri p)      = fromJust (refAppToHVM book ctx (Pri p))
  go (Pat x m c)  = patToHVM book ctx x m c

ctrToHVM :: Book -> MS.Map Name HVM.Name -> Term -> Term -> Maybe HVM.Core
ctrToHVM book ctx x y = case (x, (unsnoc (flattenTup y))) of
  (Sym k, Just (xs, One)) -> Just (HVM.Ctr ('#':defNam k) (map (termToHVM book ctx) xs))
  _ -> Nothing

valToHVM :: Book -> MS.Map Name HVM.Name -> NVal -> HVM.Core
valToHVM book ctx v = case v of
  U64_V v -> HVM.U32 (fromIntegral v)
  I64_V v -> HVM.Era
  F64_V v -> HVM.Era
  CHR_V c -> HVM.Chr c

op2ToHVM :: Book -> MS.Map Name HVM.Name -> NOp2 -> Term -> Term -> HVM.Core
op2ToHVM book ctx op a b = case op of
  ADD -> HVM.Op2 HVM.OP_ADD (termToHVM book ctx a) (termToHVM book ctx b)
  SUB -> HVM.Op2 HVM.OP_SUB (termToHVM book ctx a) (termToHVM book ctx b)
  MUL -> HVM.Op2 HVM.OP_MUL (termToHVM book ctx a) (termToHVM book ctx b)
  DIV -> HVM.Op2 HVM.OP_DIV (termToHVM book ctx a) (termToHVM book ctx b)
  MOD -> HVM.Op2 HVM.OP_MOD (termToHVM book ctx a) (termToHVM book ctx b)
  POW -> error "POW binary operator not yet supported on Bend-to-HVM compiler."
  EQL -> HVM.Op2 HVM.OP_EQ  (termToHVM book ctx a) (termToHVM book ctx b)
  NEQ -> HVM.Op2 HVM.OP_NE  (termToHVM book ctx a) (termToHVM book ctx b)
  LST -> HVM.Op2 HVM.OP_LT  (termToHVM book ctx a) (termToHVM book ctx b)
  GRT -> HVM.Op2 HVM.OP_GT  (termToHVM book ctx a) (termToHVM book ctx b)
  LEQ -> HVM.Op2 HVM.OP_LTE (termToHVM book ctx a) (termToHVM book ctx b)
  GEQ -> HVM.Op2 HVM.OP_GTE (termToHVM book ctx a) (termToHVM book ctx b)
  AND -> HVM.Op2 HVM.OP_AND (termToHVM book ctx a) (termToHVM book ctx b)
  OR  -> HVM.Op2 HVM.OP_OR  (termToHVM book ctx a) (termToHVM book ctx b)
  XOR -> HVM.Op2 HVM.OP_XOR (termToHVM book ctx a) (termToHVM book ctx b)
  SHL -> HVM.Op2 HVM.OP_LSH (termToHVM book ctx a) (termToHVM book ctx b)
  SHR -> HVM.Op2 HVM.OP_RSH (termToHVM book ctx a) (termToHVM book ctx b)

op1ToHVM :: Book -> MS.Map Name HVM.Name -> NOp1 -> Term -> HVM.Core
op1ToHVM book ctx op a = case op of
  NOT -> error "NOT unary operator not yet supported on Bend-to-HVM compiler."
  NEG -> error "NEG unary operator not yet supported on Bend-to-HVM compiler."

refAppToHVM :: Book -> MS.Map Name HVM.Name -> Term -> Maybe HVM.Core
refAppToHVM book ctx term =
  case collectApps term [] of
    (Ref k, args) ->
      let (_,tm,ty)   = fromJust (deref book k)
          (era,arg,_) = collectLamArgs tm ty [] []
          argsHVM     = map (termToHVM book ctx) (drop (length era) args)
          ari         = length arg
          len         = length argsHVM
      in return $ wrapRef (defNam k) argsHVM len ari
    (Pri p, args) -> case p of
      U64_TO_CHAR -> return $ wrapRef "U64_TO_CHAR" (map (termToHVM book ctx) args) (length args) 1
      CHAR_TO_U64 -> return $ wrapRef "CHAR_TO_U64" (map (termToHVM book ctx) args) (length args) 1
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
patToHVM :: Book -> MS.Map Name HVM.Name -> [Term] -> [Move] -> [Case] -> HVM.Core
patToHVM book ctx [x] m c@(([p], f) : _) =
  case p of
    (Var k i)    -> HVM.Let HVM.LAZY (bindNam k) (termToHVM book ctx x) (termToHVM book ctx f) -- unreachable?
    (Emp)        -> HVM.Era
    (One)        -> termToHVM book ctx f
    (Bt0)        -> bitMat
    (Bt1)        -> bitMat
    (Zer)        -> simpleMat
    (Suc _)      -> simpleMat
    (Nil)        -> simpleMat
    (Con _ _)    -> simpleMat
    (Sym _)      -> error "Nested matches on constructors and matches on symbols are not yet supported on Bend-to-HVM compiler."
    (Tup _ _)    ->
      case ctrPatToHVM book ctx x m c of
        Just hvm -> hvm
        Nothing  -> simpleMat
    (Rfl)        -> termToHVM book ctx (snd (head c))
    (Sup l (Var a _) (Var b _)) -> HVM.Ref "DUP" 0 [termToHVM book ctx l, termToHVM book ctx x, (HVM.Lam (bindNam a) (HVM.Lam (bindNam b) (termToHVM book ctx f)))]
    _ -> HVM.Era
  where
    -- A match that is contained in a single Pat term (bool, nat, list, pair)
    simpleMat = HVM.Mat (HVM.MAT 0) (termToHVM book ctx x) hvmMv sortedCs
    hvmMv     = map (\(k,v) -> (bindNam k, termToHVM book ctx v)) m
    -- Bend can output first True (1/_) and then False (0), so need to sort.
    -- A coincidence, but lexicographic string order actually works for this (vars can't start with $ but HVM already requires that)
    sortedCs  = sortBy (\(a,_,_) (b,_,_) -> compare a b) hvmCs
    hvmCs     = map (\(p,x) -> case head p of
        (Bt0)                     -> ("0", [], termToHVM book ctx x)
        (Bt1)                     -> ("_", [], termToHVM book ctx x)
        (Zer)                     -> ("#Z", [], termToHVM book ctx x)
        (Suc (Var k _))           -> ("#S", [bindNam k], termToHVM book ctx x)
        (Nil)                     -> ("#Nil", [], termToHVM book ctx x)
        (Con (Var h _) (Var t _)) -> ("#Cons", [bindNam h, bindNam t], termToHVM book ctx x)
        (Tup (Var a _) (Var b _)) -> ("#P", [bindNam a, bindNam b], termToHVM book ctx x)
        _                         -> ("_", [], termToHVM book ctx x)
      ) goodCs
    goodCs = filter (not . badPatCase) c
    bitMat = case c of
      (([Bt0],f):([Bt1],t):_) -> tm (termToHVM book ctx f) (termToHVM book ctx t)
      (([Bt1],t):([Bt0],f):_) -> tm (termToHVM book ctx f) (termToHVM book ctx t)
      (([Bt0],f):([Var k _],t):_) -> tm (termToHVM book ctx f) (HVM.Let HVM.LAZY k (HVM.Op2 HVM.OP_ADD (HVM.U32 1) (HVM.Var "bp$")) (termToHVM book ctx t))
      (([Bt1],f):([Var k _],t):_) -> tm (HVM.Let HVM.LAZY k (HVM.U32 0) (termToHVM book ctx f)) (termToHVM book ctx t)
      _ -> HVM.Era
      where tm f t = HVM.Mat HVM.SWI (termToHVM book ctx x) hvmMv [("0", [], f), ("1+bp$", [], t)]
patToHVM book ctx x m c = HVM.Era

-- Since ctrs are desugared to a Sym + some Tups, the nested matches on the fields happen before the Tup matches on the entire constructor.
-- We need to somehow reorder the cases so that firsdt we match on the entire constructor and only then on the fields.
ctrPatToHVM :: Book -> MS.Map Name HVM.Name -> Term -> [Move] -> [Case] -> Maybe HVM.Core
ctrPatToHVM book ctx x m c = case c of
  (([Tup (Var a _) (Var kB _)], Pat [(Var k _)] _ c) : _) ->
    if a == k then do
      let mv = map (\(k,v) -> (bindNam k, termToHVM book ctx v)) m
      cs <- mapM (\(p, x) -> case head p of
          Sym ctr  -> caseToHVM ctr [] x
          Var kT _ -> return (bindNam kT, [], rewriteDflt kT kB (termToHVM book ctx x))
          _ -> Nothing
        ) (filter (not . badPatCase) c)
      return $ HVM.Mat (HVM.MAT 0) (termToHVM book ctx x) mv cs
    else Nothing
  _ -> Nothing
  where
    caseToHVM :: Name -> [Name] -> Term ->  Maybe HVM.Case
    caseToHVM ctr fds (Pat [(Var k _)] _ (([(Tup (Var a _) (Var b _))], bod) : _)) = caseToHVM ctr (fds ++ [a]) bod
    caseToHVM ctr fds (Pat [(Var k _)] _ (([One], bod) : _)) = Just ('#':defNam ctr, map bindNam fds, termToHVM book ctx bod)
    caseToHVM _ _ _ = Nothing

    rewriteDflt kT kB x = rewriteHVM (HVM.Ctr "#P" [HVM.Var kT, HVM.Var kB]) (HVM.Var kT) x


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
    go (HVM.Dup l x y v f) = "! &" ++ show l ++ "{" ++ x ++ " " ++ y ++ "} = " ++ showHVM lv v ++ "\n" ++ indent lv ++ showHVM lv f
    go (HVM.Ctr k [])      = k
    go (HVM.Ctr k xs)      = k ++ "{" ++ unwords (map (showHVM lv) xs) ++ "}"
    go (HVM.U32 v)         = show v
    go (HVM.Chr v)         = "'" ++ [v] ++ "'"
    go (HVM.Op2 o a b)     = "(" ++ show o ++ " " ++ showHVM lv a ++ " " ++ showHVM lv b ++ ")"
    go (HVM.Let m k v f)   = "! " ++ show m ++ k ++ " = " ++ showHVM (lv+1) v ++ "\n" ++ indent lv ++ showHVM lv f
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










