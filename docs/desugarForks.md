
# Fork Desugaring Algorithm

The Fork Desugaring module transforms high-level `fork` expressions into low-level superposition constructs, enabling parallel execution by duplicating the execution context across both branches of the fork.

## Overview

The main goal is to eliminate all `Frk` terms from expressions by converting them into explicit superpositions (`Sup`) with appropriately duplicated variable contexts. This transformation is essential for Bend's parallel execution model.

```haskell
Frk Term Term Term  -- fork L: A else: B
```

Gets transformed into a chain of superposed variables and a final superposition of the two branches.

## Algorithm Components

### 1. Entry Point (`desugarFrks`)

```haskell
desugarFrks :: Book -> Int -> Term -> Term
desugarFrks book d term = desugarFrksGo book d [] term
```

The entry point initializes the recursive transformation with:
- **Book**: Definition context for reference resolution
- **Int**: Initial binding depth (usually 0)
- **Empty context**: `[]` - no variables in scope initially

### 2. Main Recursion (`desugarFrksGo`)

```haskell
desugarFrksGo :: Book -> Int -> [(Name, Int)] -> Term -> Term
```

This function performs a depth-first traversal of the term structure, maintaining a **variable context** `[(Name, Int)]` that tracks:
- **Name**: Variable identifier
- **Int**: Binding depth where the variable was introduced

#### Context Building

The context grows as we traverse binding constructs:

```haskell
-- Lambda binding: parameter enters scope at current depth
desugarFrksGo book d ctx (Lam n t f) =
  Lam n (fmap (desugarFrksGo book d ctx) t)
    (\x -> desugarFrksGo book (d+1) ((n,d):ctx) (f x))
    --                          ^^^^^^^^^^^^^^^^
    --                          Add parameter to context

-- Let binding: bound variable enters scope
desugarFrksGo book d ctx (Let k t v f) =
  Let k (fmap (desugarFrksGo book d ctx) t)
        (desugarFrksGo book d ctx v)
    (\x -> desugarFrksGo book (d+1) ((k,d):ctx) (f x))
    --                          ^^^^^^^^^^^^^^^^
    --                          Add let-variable to context
```

Similar context updates occur for:
- **`Use k v f`**: Adds usage variable `k` to context
- **`Fix k f`**: Adds recursive variable `k` to context
- **`Pat s m c`**: Adds pattern variables and move variables to context

#### Fork Detection

When a `Frk l a b` is encountered, the algorithm delegates to the specialized transformation:

```haskell
desugarFrksGo book d ctx (Frk l a b) = desugarFrk book d ctx l a b
```

### 3. Fork Transformation (`desugarFrk`)

This is the core transformation that converts a single fork into superpositions:

```haskell
desugarFrk :: Book -> Int -> [(Name, Int)] -> Term -> Term -> Term -> Term
desugarFrk book d ctx l a b = buildSupMs vars
```

#### Step 1: Variable Analysis

```haskell
vars = shadowCtx (filter (\x -> fst x `S.member` free) (reverse ctx))
free = case cut l of
  Var n _ -> S.delete n (freeVars S.empty a `S.union` freeVars S.empty b)
  _       -> freeVars S.empty a `S.union` freeVars S.empty b
```

The algorithm:
1. **Collects free variables**: Finds all variables used in branches `a` and `b`
2. **Optimizes label variable**: If the fork label `l` is a simple variable, excludes it from duplication
3. **Filters relevant context**: Only keeps context variables that are actually used
4. **Removes shadowing**: Uses `shadowCtx` to eliminate duplicate variable names

#### Step 2: Context Superposition (`buildSupMs`)

This creates nested superposition matchers for each context variable:

```haskell
buildSupMs :: [(Name, Int)] -> Term
-- Base case: no more variables to superpose
buildSupMs [] = Sup l a' b' where
  ls = [(n, Var (n++"0") 0) | (n, _) <- vars]  -- Left substitutions
  rs = [(n, Var (n++"1") 0) | (n, _) <- vars]  -- Right substitutions
  a' = bindVarByNameMany ls (desugarFrksGo book d ctx a)
  b' = bindVarByNameMany rs (desugarFrksGo book d ctx b)

-- Recursive case: create SupM for current variable
buildSupMs ((n,d):rest) =
  App (SupM l $
       Lam (n++"0") Nothing $ \_ ->
       Lam (n++"1") Nothing $ \_ ->
       buildSupMs rest) (Var n d)
```

#### Step 3: Variable Duplication Strategy

For each context variable `x`, the transformation creates:
- **`x0`**: Version used in the left branch (`a`)
- **`x1`**: Version used in the right branch (`b`)
- **`SupM l (λx0. λx1. ...)`**: Superposition matcher applied to original `x`

#### Step 4: Shadow Context Resolution (`shadowCtx`)

```haskell
shadowCtx ((n,d):ctx) =
  if n `elem` (map fst ctx)
    then shadowCtx ctx        -- Skip shadowed variable
    else (n,d) : shadowCtx ctx -- Keep unique variable
shadowCtx [] = []
```

This removes duplicate variable names, keeping only the most recent binding (lexical scoping).

## Transformation Example

### Input Code
```bend
λx. λy.
  let z = x + y in
    fork L: (x + z) else: (y * z)
```

### Context at Fork
```haskell
ctx = [("z", 2), ("y", 1), ("x", 0)]
```

### Transformation Steps

1. **Variable Analysis**: All variables `x`, `y`, `z` are used in both branches
2. **Superposition Generation**: Create `SupM` for each variable
3. **Final Result**:

```bend
λx. λy.
  let z = x + y in
    SupM L (λx0. λx1.           -- Superpose x
      SupM L (λy0. λy1.         -- Superpose y
        SupM L (λz0. λz1.       -- Superpose z
          Sup L (x0 + z0)       -- Left branch with x0, z0
                (y1 * z1)       -- Right branch with y1, z1
        ) z
      ) y
    ) x
```

### Runtime Behavior

When executed, this creates a superposition network where:
- `x` splits into `x0` (left) and `x1` (right)
- `y` splits into `y0` (left) and `y1` (right)
- `z` splits into `z0` (left) and `z1` (right)
- Left branch computes `x0 + z0`
- Right branch computes `y1 * z1`
- Both execute in parallel

## Key Properties

1. Context Preservation: All variables in scope are properly superposed
2. Parallel Execution: Both branches can execute simultaneously
3. Variable Isolation: Each branch gets its own copy of all context variables
4. Binding Depth Tracking: Maintains correct variable references across transformations
5. Shadowing Respect: Inner variable bindings properly shadow outer ones

