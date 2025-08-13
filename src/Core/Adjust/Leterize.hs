{-# LANGUAGE ViewPatterns #-}
module Core.Adjust.Leterize where

import Core.Type
import Core.Show
import Core.Bind
import Core.Adjust.ReduceEtas
import qualified Data.Map as M

import Control.Applicative
import Debug.Trace

extend :: Ctx -> Name -> Term -> Term -> Ctx
extend (Ctx ctx) k v t = Ctx (ctx ++ [(k, v, t)])

dependencyInfer :: Int -> Book -> Ctx -> Term -> Term -> Term -> Either Term Term
dependencyInfer d book ctx@(Ctx ctxl) goal term def = trace ("-depInfer: " ++ show term) $
  case term of
  Var k i -> Right def
  Ref n i -> Right def
  Sub t -> dependencyInfer d book ctx goal t def
  Fix k f -> dependencyInfer (d+1) book ctx goal (f (Var k d)) def
  Let k ty v f -> do
    case ty of
      Just t  -> dependencyInfer d book ctx goal t def
      Nothing -> Right def
    dependencyInfer d book ctx goal v def
    dependencyInfer d book ctx goal (f (Var k d)) def
  Use k v f -> do
    dependencyInfer d book ctx goal v def
    dependencyInfer d book ctx goal (f (Var k d)) def
  Set -> Right def
  Chk x ty -> do
    dependencyInfer d book ctx goal x def
    dependencyInfer d book ctx goal ty def
  Emp -> Right def
  EmpM -> Right def
  Uni -> Right def
  One -> Right def
  UniM f -> dependencyInfer d book ctx goal f def
  Bit -> Right def
  Bt0 -> Right def
  Bt1 -> Right def
  BitM f t -> do
    dependencyInfer d book ctx goal f def
    dependencyInfer d book ctx goal t def
  Nat -> Right def
  Zer -> Right def
  Suc n -> dependencyInfer d book ctx goal n def
  NatM z s -> do
    dependencyInfer d book ctx goal z def
    dependencyInfer d book ctx goal s def
  Lst ty -> dependencyInfer d book ctx goal ty def
  Nil -> Right def
  Con h t -> do
    dependencyInfer d book ctx goal h def
    dependencyInfer d book ctx goal t def
  LstM n c -> do
    dependencyInfer d book ctx goal n def
    dependencyInfer d book ctx goal c def
  Enu ss -> Right def
  Sym s -> Right def
  EnuM cs e -> do
    mapM_ (\(s, v) -> dependencyInfer d book ctx goal v def) cs
    dependencyInfer d book ctx goal e def
  Num nt -> Right def
  Val nv -> Right def
  Op2 o a b -> do
    dependencyInfer d book ctx goal a def
    dependencyInfer d book ctx goal b def
  Op1 o a -> dependencyInfer d book ctx goal a def
  Sig a b -> do
    dependencyInfer d book ctx goal a def
    dependencyInfer d book ctx goal b def
  Tup a b -> do
    dependencyInfer d book ctx goal a def
    dependencyInfer d book ctx goal b def
  SigM f -> dependencyInfer d book ctx goal f def
  All a b -> do
    dependencyInfer d book ctx goal a def
    dependencyInfer d book ctx goal b def
  Lam k ty f -> do
    case ty of
      Just t -> dependencyInfer d book ctx goal t def
      Nothing -> Right def
    dependencyInfer (d+1) book ctx goal (f (Var k d)) def
  App f x -> do
    let fRes = greedyInfer d book ctx goal f
    case fRes of
      All a b -> Left a  -- Short-circuit with Left a
      _ -> dependencyInfer d book ctx goal x def
  Eql ty a b -> do
    dependencyInfer d book ctx goal ty def
    dependencyInfer d book ctx goal a def
    dependencyInfer d book ctx goal b def
  Rfl -> Right def
  EqlM f -> dependencyInfer d book ctx goal f def
  Rwt e f -> do
    dependencyInfer d book ctx goal e def
    dependencyInfer d book ctx goal f def
  Met n ty as -> do
    dependencyInfer d book ctx goal ty def
    mapM_ (dependencyInfer d book ctx goal `flip` def) as
    Right def
    where flip f a b = f a b
  Era -> Right def
  Sup l a b -> do
    dependencyInfer d book ctx goal l def
    dependencyInfer d book ctx goal a def
    dependencyInfer d book ctx goal b def
  SupM l f -> do
    dependencyInfer d book ctx goal l def
    dependencyInfer d book ctx goal f def
  Loc s t -> dependencyInfer d book ctx goal t def
  Log s x -> do
    dependencyInfer d book ctx goal s def
    dependencyInfer d book ctx goal x def
  Pri p -> Right def
  Pat ss ms cs -> do
    mapM_ (dependencyInfer d book ctx goal `flip` def) ss
    mapM_ (\(s, t) -> dependencyInfer d book ctx goal t def) ms
    mapM_ (\(ts, t) -> do
             mapM_ (dependencyInfer d book ctx goal `flip` def) ts
             dependencyInfer d book ctx goal t def) cs
    Right def
    where flip f a b = f a b
  Frk l a b -> do
    dependencyInfer d book ctx goal l def
    dependencyInfer d book ctx goal a def
    dependencyInfer d book ctx goal b def

greedyInfer :: Int -> Book -> Ctx -> Type -> Term -> Type
-- greedyInfer d book ctx@(Ctx ctxl) goal term = trace ("-ginfer: " ++ show term) $ -- TODO: not everything here is well thought
greedyInfer d book ctx@(Ctx ctxl) goal term =  -- TODO: not everything here is well thought
  case term of
  Var k i -> do
      case reverse $ filter (\(nam, _, _) -> nam == k) ctxl of -- picking the last takes shadowing into account
        (_, _, typ):_ -> typ
        [] -> error "greedInfer: variable is not in context"
  Ref n i -> case book of
      Book defns _ -> case M.lookup n defns of
          Just (_, _, typ) -> typ
          Nothing -> error "greedyInfer: reference is not in book"
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
  NatM z s -> case cut s of
    Lam p mt b -> All Nat (NatM (greedyInfer d book ctx goal z) (Lam p mt (\_ -> (greedyInfer (d+1) book ctx goal (b (Var p d))))))
    s          -> All Nat (NatM (greedyInfer d book ctx goal z) (greedyInfer d book ctx goal s))
  Lst ty      -> Set
  Nil         -> error "greedyInfer: Nil undefined"
  Con h t     -> Lst (greedyInfer d book ctx goal h)
  LstM n c    -> All (Lst (greedyInfer d book ctx goal n)) (Lam "_" Nothing (\_ -> LstM (greedyInfer d book ctx goal n) (greedyInfer d book ctx goal c))) -- TODO: think
  Enu ss      -> Set
  Sym s       -> error "greedyInfer: Sym undefined"
  EnuM cs e   -> EnuM [(s, greedyInfer d book ctx goal v) | (s, v) <- cs] (greedyInfer d book ctx goal e) -- TODO: think
  Num nt      -> Set
  Val nv      -> case nv of
    U64_V _ -> Num U64_T
    I64_V _ -> Num I64_T
    F64_V _ -> Num F64_T
    CHR_V _ -> Num CHR_T
  Op2 o a b   -> greedyInfer d book ctx goal a -- TODO: think
  Op1 o a     -> greedyInfer d book ctx goal a -- TODO: think
  Sig a b     -> Set
  Tup a b     -> Sig (greedyInfer d book ctx goal a) (Lam "_" Nothing (\_ -> greedyInfer d book ctx goal b)) -- TODO: think
  SigM f      -> error "greedyInfer: SigM undefined"
  All a b     -> Set
  Lam k ty f  -> error "greedyInfer: Lam undefined"
  App f x     -> case trace ("IIIII " ++ show f) $ greedyInfer d book ctx goal f of
    All a b -> b
    fT      -> goal  -- fallback to goal if not a function type
  Eql ty a b  -> Set
  Rfl         -> error "greedyInfer: Rfl undefined"
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
  App f x -> if isLamMatch (cut f)
    then
      let k = "$aux_" ++ show j
          fT = case cut f of
            SigM b -> 
              case inferDependentPairType d book ctx f x typ of
                Just (domType, codType) -> 
                  let result = All domType codType
                  in
                  -- trace ("WIP: domain/codomain(" ++ show f ++ ", " ++ show x ++ ") = " ++ show (Just (domType, codType))) $
                  result
                Nothing -> 
                  -- trace ("WIP: domain/codomain(" ++ show f ++ ", " ++ show x ++ ") = Nothing") $
                  greedyInfer d book ctx typ f
            _ -> greedyInfer d book ctx typ f
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

-- Builds the codomain type based on the value of the pair (a, b)
buildCodomainType :: Int -> Book -> Ctx -> Term -> String -> String -> Term -> Term
buildCodomainType d book ctx defaultCodomain aParam bParam etaReduced = 
  case cut etaReduced of
    -- When we find both a and b bound, we can infer the actual codomain type
    Use k v f | k == aParam -> 
      -- Continue looking for b binding
      buildCodomainType d book (extend ctx k v (greedyInfer d book ctx Set v)) defaultCodomain aParam bParam (f v)
    
    Use k v f | k == bParam ->
      -- Both a and b are now fixed, infer the codomain type
      greedyInfer d book (extend ctx k v (greedyInfer d book ctx Set v)) Set (f v)
    
    -- Pattern matches - recurse into branches
    NatM z s -> 
      NatM (buildCodomainType d book ctx defaultCodomain aParam bParam z)
           (buildCodomainType d book ctx defaultCodomain aParam bParam s)
    
    BitM f t ->
      BitM (buildCodomainType d book ctx defaultCodomain aParam bParam f)
           (buildCodomainType d book ctx defaultCodomain aParam bParam t)
    
    -- Pattern match on pairs - this is the SigM case
    SigM f ->
      SigM (buildCodomainType d book ctx defaultCodomain aParam bParam f)
    
    -- Lambdas - these represent pattern match continuations
    Lam k ty f ->
      Lam k ty (\x -> buildCodomainType (d+1) book ctx defaultCodomain aParam bParam (f x))
    
    -- Default: when we reach a term that doesn't bind our variables, 
    -- infer its type as the codomain for this branch
    t -> greedyInfer d book ctx Set t

-- Builds the dependent type function for b based on the value of a
buildBTypeFunc :: Int -> Book -> Ctx -> Term -> String -> String -> Term -> Term
buildBTypeFunc d book ctx defaultBType aParam bParam etaReduced = 
  case cut etaReduced of
    -- First, skip past the outer SigM and lambda structure to get to the meat
    SigM body -> buildBTypeFunc d book ctx defaultBType aParam bParam body
    
    Lam k ty f | k == aParam -> 
      -- This is the lambda binding 'a', continue into body
      Lam k ty (\x -> buildBTypeFunc (d+1) book ctx defaultBType aParam bParam (f x))
    
    Lam k ty f | k == bParam ->
      -- This is the lambda binding 'b', now look for pattern matches on 'a'
      buildBTypeFunc d book ctx defaultBType aParam bParam (f (Var bParam d))
    
    -- Pattern match on a value - this structures the dependent type
    NatM z s -> 
      -- This is a pattern match, likely on 'a' or something derived from it
      NatM (buildBTypeFunc d book ctx defaultBType aParam bParam z)
           (buildBTypeFunc d book ctx defaultBType aParam bParam s)
    
    BitM f t ->
      BitM (buildBTypeFunc d book ctx defaultBType aParam bParam f)
           (buildBTypeFunc d book ctx defaultBType aParam bParam t)
    
    -- Found where 'a' gets bound to a concrete value!
    Use k v f | k == aParam -> 
      -- Now 'a' is fixed to value v
      -- Look for what type 'b' gets in this branch
      findBType d book (extend ctx k v (greedyInfer d book ctx Set v)) bParam (f v) defaultBType
    
    -- Other lambdas - continue traversing
    Lam k ty f ->
      Lam k ty (\x -> buildBTypeFunc (d+1) book ctx defaultBType aParam bParam (f x))
    
    -- Default: no pattern matching on 'a', so 'b' has default type
    _ -> defaultBType

findBType :: Int -> Book -> Ctx -> String -> Term -> Term -> Term
findBType d book ctx bParam term defaultBType =
  case dependencyInfer d book ctx Set term defaultBType of
    Left inferredType -> inferredType
    Right _ -> defaultBType

-- Infers the type of a SigM pattern match function
-- Returns: Maybe (domain type, codomain type)
inferDependentPairType :: Int -> Book -> Ctx -> Term -> Term -> Term -> Maybe (Term, Term)
inferDependentPairType d book ctx sigm@(cut -> (SigM body)) (cut -> (Tup a b)) typ = 
  case cut body of
    Lam aParam mta innerBody -> 
      case cut (innerBody (Var aParam d)) of
        Lam bParam mtb finalBody ->
          -- Get the types of 'a' and 'b' (default)
          let aType = greedyInfer d book ctx typ a
              ctxWithA = extend ctx aParam a aType
              bDefaultType = greedyInfer d book ctxWithA typ b
              
              -- Apply reduceEtas and bind to expose the pattern structure
              -- etaReduced = bind (reduceEtas d body) -- TODO: bind doesn't know about the depth
              -- etaReduced = reduceEtas d (innerBody (Var aParam d)) -- TODO: bind doesn't know about the depth
              etaReduced = reduceEtas d body -- TODO: bind doesn't know about the depth
              
              -- Build the dependent type function for b (no wrapping Lam!)
              bTypeFunc = buildBTypeFunc d book ctx bDefaultType aParam bParam etaReduced             
              -- Build the domain type (Sigma type)
              domainType = Sig aType bTypeFunc
              
              -- Build context with a and b typed
              -- Use the dependent type for b!
              bType = App bTypeFunc a
              ctxWithAB = extend ctxWithA bParam b bType
              defaultCodomain = greedyInfer (d+2) book ctxWithAB typ (finalBody b)

              -- For codomainType: use eta-reduced full SigM (with wrapper)
              etaReducedSigM = reduceEtas d sigm
              -- Infer the codomain type
              -- codomainType = greedyInfer (d+2) book ctxWithAB typ (finalBody (Var bParam (d+1)))
              codomainType = buildCodomainType d book ctx defaultCodomain aParam bParam etaReducedSigM
       
          in
          -- trace ("eta reduced: " ++ show etaReduced) $
          Just (domainType, codomainType)
        
        _ -> Nothing  -- Inner body is not a lambda
    
    _ -> Nothing  -- Body is not a lambda

inferDependentPairType _ _ _ _ _ _ = Nothing
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
