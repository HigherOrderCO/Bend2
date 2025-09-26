
# Pattern Flattening Algorithm

The `FlattenPats` module converts pattern matching expressions with multiple scrutinees into nested case trees with single scrutinees, helping to transform Bend code into proper case-tree form.

## Overview

The algorithm preserves HOAS (Higher-Order Abstract Syntax) while recursively transforming terms. The main transformation occurs when encountering a `Pat` term:

```haskell
Pat [Term] [Move] [Case] -- match x y z { with k=v ; case @A p q: F ; ... }
```

This represents:
- **`[Term]`**: List of scrutinees to match against
- **`[Move]`**: List of 'with' bindings (variable assignments)
- **`[Case]`**: List of pattern cases with their right-hand sides

## Algorithm Steps

### 1. Main Recursion (`flattenPats`)

The algorithm recursively descends through the term structure, applying special handling only to `Pat` terms. All other term constructors are processed recursively while preserving their structure.

### 2. Pattern Flattening (`flattenPat`/`flattenPatGo`)

When a `Pat` term is encountered, the core flattening logic begins:

#### Case A: All-Variable Column
If the first pattern column consists entirely of variables (default cases):

```bend
match x y { case x0 @A: F(x0) ; case x1 @B: F(x1) }
```

This is transformed using `joinVarCol` into:

```bend
match y { with k=x ; case @A: F(k) ; case @B: F(k) }
```

The algorithm then recursively flattens the resulting pattern with the joined 'with' statement.

#### Case B: Constructor Column
If the first pattern column contains constructors:

1. **Extract Constructor**: Use `ctrOf` to get a single-layer constructor template, replacing fields with fresh pattern variables
2. **Peel Cases**: Use `peelCtrCol` to separate cases that match this constructor from those that don't
3. **Create Binary Split**: Generate a pattern with exactly two cases:
   - **Constructor branch**: Matches the specific constructor, continues with remaining scrutinees
   - **Default branch**: Catches all other cases with a fresh variable

```bend
-- Before flattening
match x y:
  case 0n     0n: A
  case (1n+x) 0n: B
  case 0n     (1n+y): C

-- After one flattening step
match x:
  case 0n:
    match y:
      case 0n: A
      case 1n+y: C
  case _fresh:
    match _fresh y:
      case (1n+x) 0n: B
```

### 3. Constructor Peeling (`peelCtrCol`)

This function separates cases based on whether they match a specific constructor:

```haskell
-- Input cases:
--   case @Z{}      @A: A
--   case @S{@Z}    @B: B
--   case @S{@S{p}} @C: C(p)
--
-- Peeling @Z and @S{k} produces:
-- Picks (match @Z):     [case @A: A]
-- Picks (match @S{k}):  [case @Z @B: B, case @S{p} @C: C(p)]
-- Drops:                [remaining unmatched cases]
```

The function handles various constructor types:
- **Nat**: `Zer`, `Suc`
- **Bool**: `Bt0`, `Bt1`
- **List**: `Nil`, `Con`
- **Unit**: `One`
- **Pair**: `Tup`
- **Symbol**: `Sym`
- **Equality**: `Rfl`
- **Superposition**: `Sup`

For each constructor type, it:
- Extracts sub-patterns for matching cases
- Generates appropriate variable bindings for default cases
- Handles location information preservation

### 4. Post-Processing (`simplify`/`merge`)

After flattening, the algorithm cleans up redundant nested matches:

```haskell
-- Before simplification
match x: case y: match y { case A: expr_A ; case B: expr_B }

-- After simplification
match x: case A: expr_A ; case B: expr_B
```

### 5. Base Cases

- **Empty scrutinees**: `Pat [] ms (([],rhs):cs)` → return `rhs`
- **Empty cases**: `Pat (_:_) _ []` → return unchanged
- **Location preservation**: Maintains source location information through transformations

## Key Properties

1. **Single Scrutinee Output**: Each flattened pattern matches exactly one scrutinee
2. **Binary Branching**: Complex multi-way matches become nested binary decisions
3. **HOAS Preservation**: Higher-order abstract syntax is maintained throughout
4. **Proper Case-Tree Form**: Output conforms to Bend's canonical case-tree structure
5. **Exhaustiveness**: All original cases are preserved in the flattened form

## Example Transformation

```bend
-- Input: Multi-scrutinee pattern
match x y:
  case 0n     0n: A
  case (1n+p) 0n: B
  case 0n     (1n+q): C
  case (1n+p) (1n+q): D

-- Output: Nested single-scrutinee patterns
match x:
  case 0n:
    match y:
      case 0n: A
      case 1n+q: C
  case 1n+p:
    match y:
      case 0n: B
      case 1n+q: D
```

This flattening enables Bend to generate efficient lambda-match expressions and ensures compatibility with the HVM runtime's pattern matching semantics.
