# Bend Type System Guide

Bend features a rich dependent type system that allows you to express precise specifications and verify them at compile time. This guide covers the type system from basic concepts to advanced features.

## Table of Contents

- [Type Hierarchy](#type-hierarchy)
- [Basic Types](#basic-types)
- [Function Types](#function-types)
- [Dependent Types](#dependent-types)
- [Equality Types](#equality-types)
- [Inductive Types](#inductive-types)
- [Type Inference](#type-inference)
- [Advanced Features](#advanced-features)
- [Practical Examples](#practical-examples)

## Type Hierarchy

Bend's type system follows a simple hierarchy:

```
Set : Set    (impredicative universe)
```

All types have type `Set`, including `Set` itself (impredicative). This makes the system very expressive but requires care to avoid paradoxes.

## Basic Types

### Primitive Types

```bend
Set      # The type of types
Empty    # The empty type (⊥) - has no values
Unit     # The unit type - has exactly one value: ()
Bool     # Boolean type - has two values: True, False
Nat      # Natural numbers - 0n, 1n, 2n, ...
```

### Numeric Types

```bend
U64      # 64-bit unsigned integers: 0, 1, 2, ..., 2^64-1
I64      # 64-bit signed integers: -2^63, ..., -1, 0, 1, ..., 2^63-1
F64      # 64-bit floating point numbers
Char     # Unicode characters
```

### Compound Types

```bend
A[]             # Lists of type A
A & B           # Product types (pairs)
A -> B          # Function types
enum{&A, &B}    # Enumeration types
```

## Function Types

### Simple Function Types

```bend
Nat -> Nat              # Functions from Nat to Nat
Bool -> Nat -> Bool     # Curried function (Bool -> (Nat -> Bool))
```

### Multi-argument Functions

Functions in Bend are curried by default:

```bend
# This function type:
(Nat, Bool) -> String

# Is sugar for:
Nat -> Bool -> String

# Which is sugar for:
Nat -> (Bool -> String)
```

Example:
```bend
def example(n: Nat, b: Bool) -> String:
  if b:
    "number: " ++ show(n)
  else:
    "hidden"

# Usage:
example(42n, True)           # Apply both arguments
partially_applied = example(42n)  # Partial application
```

## Dependent Types

### Dependent Function Types (Π-types)

Dependent function types allow the return type to depend on the input value:

```bend
# Syntax: ∀x:A. B(x)  or  all x:A. B(x)

# Example: A function that returns a vector of the specified length
def replicate<A>(n: Nat, x: A) -> Vec<A, n>:
  match n:
    case 0n:
      @Nil{{==}}
    case 1n + m:
      @Cons{m, x, replicate<A>(m, x), {==}}

# The type of replicate is:
# ∀A:Set. ∀n:Nat. A -> Vec<A, n>
```

### Dependent Pair Types (Σ-types)

Dependent pairs allow the second component's type to depend on the first:

```bend
# Syntax: any x:A. B(x)  or  Σx:A. B(x)

# Example: A pair of a natural number and a vector of that length
def sized_vector<A>() -> any n:Nat. Vec<A, n>:
  (3n, @Cons{2n, value1, @Cons{1n, value2, @Cons{0n, value3, @Nil{{==}}, {==}}, {==}}, {==}})
```

### Index Types and Families

Types can be parameterized by values (indices):

```bend
# Vec is indexed by both a type and a natural number
type Vec<A: Set>(N: Nat) -> Set:
  case @Nil:
    e: Nat{N == 0n}
  case @Cons:
    n: Nat
    head: A
    tail: Vec<A, n>
    e: Nat{N == 1n + n}

# Usage examples:
empty_vec : Vec<Nat, 0n> = @Nil{{==}}
single_vec : Vec<Bool, 1n> = @Cons{0n, True, @Nil{{==}}, {==}}
```

## Equality Types

### Propositional Equality

Bend's equality types express that two terms are equal:

```bend
# Syntax: T{a == b}
# Read as: "Type T such that a equals b"

# Examples:
Nat{2n + 3n == 5n}          # Proof that 2+3 equals 5
Bool{True == True}          # Proof that True equals True
A{f(g(x)) == h(x)}          # Proof of function equality
```

### Inequality Types

```bend
# Syntax: T{a != b}
# Desugars to: Not(T{a == b})

# Examples:
Nat{0n != 1n}               # Proof that 0 doesn't equal 1
Bool{True != False}         # Proof that True doesn't equal False
```

### Working with Equality

```bend
# Reflexivity: every term equals itself
def refl<A>(x: A) -> A{x == x}:
  {==}

# Symmetry: if a = b then b = a  
def sym<A>(a: A, b: A, e: A{a == b}) -> A{b == a}:
  rewrite e
  {==}

# Transitivity: if a = b and b = c then a = c
def trans<A>(a: A, b: A, c: A, e1: A{a == b}, e2: A{b == c}) -> A{a == c}:
  rewrite e1
  rewrite e2
  {==}

# Congruence: if a = b then f(a) = f(b)
def cong<A, B>(a: A, b: A, f: A -> B, e: A{a == b}) -> B{f(a) == f(b)}:
  rewrite e
  {==}
```

## Inductive Types

### Simple Inductive Types

```bend
# Natural numbers (built-in, but could be defined as):
type Nat:
  case @Zero:
  case @Succ:
    pred: Nat

# Lists
type List<A: Set>:
  case @Nil:
  case @Cons:
    head: A
    tail: List<A>
```

### Indexed Inductive Types

These are inductive types that carry additional information in their indices:

```bend
# Vectors (lists with length in the type)
type Vec<A: Set>(N: Nat) -> Set:
  case @Nil:
    e: Nat{N == 0n}
  case @Cons:
    n: Nat
    head: A
    tail: Vec<A, n>
    e: Nat{N == 1n + n}

# Well-founded trees
type WTree<A: Set>:
  case @Leaf:
    value: A
  case @Node:
    children: WTree<A>[]
```

### Induction Principles

Each inductive type automatically gets an induction principle:

```bend
# Natural number induction
def nat_induction
  ( P: Nat -> Set                    # Property to prove
  , base: P(0n)                      # Base case
  , step: ∀n:Nat. P(n) -> P(1n + n)  # Inductive step
  , n: Nat                           # Number to prove property for
  ) -> P(n):
  match n:
    case 0n:
      base
    case 1n + m:
      step(m, nat_induction(P, base, step, m))
```

## Type Inference

### What Bend Infers

Bend has **no type inference**. This means:

1. **All type parameters must be explicit**:
   ```bend
   # Wrong:
   map(double, [1n, 2n, 3n])
   
   # Correct:
   map<Nat, Nat>(double, [1n, 2n, 3n])
   ```

2. **Function signatures must be complete**:
   ```bend
   # Wrong:
   def mystery(x):
     x + 1n
   
   # Correct:
   def mystery(x: Nat) -> Nat:
     x + 1n
   ```

### Why No Inference?

The lack of inference is intentional:
- Makes types explicit and readable
- Avoids complex inference algorithms
- Makes type errors predictable
- Helps with proof construction

## Advanced Features

### Higher-Order Types

Types can be parameterized by other types:

```bend
# Functor-like type constructor
def Functor(F: Set -> Set) -> Set:
  ∀A B:Set. (A -> B) -> F(A) -> F(B)

# Example instance for Maybe
def maybe_functor() -> Functor(Maybe):
  λA B f opt.
    match opt:
      case @None{}:
        @None{}
      case @Some{x}:
        @Some{f(x)}
```

### Universe Polymorphism

Bend uses an impredicative `Set`:

```bend
# This is valid (Set : Set)
def type_of_set() -> Set:
  Set

# This allows powerful abstractions
def identity_type<A: Set>() -> Set:
  A -> A
```

### Proof Irrelevance

Equality proofs are computationally irrelevant:

```bend
# These two proofs are definitionally equal
proof1 : Nat{2n + 2n == 4n} = {==}
proof2 : Nat{2n + 2n == 4n} = {==}

# They both reduce to the same canonical form
```

## Practical Examples

### Safe Array Access

```bend
type SafeArray<A: Set>(N: Nat) -> Set:
  case @Array:
    data: A[]
    len: Nat
    proof: Nat{length<A>(data) == N}

def safe_get<A>(n: Nat, i: Nat, arr: SafeArray<A, n>, proof: Nat{i < n}) -> A:
  # Implementation would check bounds using the proof
  unsafe_get(i, arr.data)
```

### Certified Sorting

```bend
# Predicate for sorted lists
def is_sorted(xs: Nat[]) -> Bool:
  match xs:
    case []:
      True
    case [x]:
      True
    case x <> y <> rest:
      if x <= y:
        is_sorted(y <> rest)
      else:
        False

# Sorting function with proof
def certified_sort(xs: Nat[]) -> any ys:Nat[]. (Nat{is_sorted(ys) == True} & Nat{same_elements(xs, ys) == True}):
  # Implementation would return sorted list with proofs
  ()
```

### Dependent Pattern Matching

```bend
def vec_head<A>(n: Nat, v: Vec<A, 1n + n>) -> A:
  match v:
    case @Nil{e}:
      # Here e : Nat{1n + n == 0n}
      # This is impossible, so we can derive anything
      absurd e
    case @Cons{m, head, tail, e}:
      # Here e : Nat{1n + n == 1n + m}
      # We can deduce that n == m
      head
```

### Type-Level Computation

```bend
# Type-level addition
def add_types(n: Nat, m: Nat) -> Set:
  Vec<Unit, n + m>

# Proof that type-level addition is commutative
def add_types_comm(n: Nat, m: Nat) -> (add_types(n, m) -> add_types(m, n)):
  λv. transport(add_comm(n, m), v)
```

## Common Type Errors

### 1. Missing Type Parameters

```bend
# Error: Cannot infer type parameters
map(double, numbers)

# Fix: Provide explicit type parameters
map<Nat, Nat>(double, numbers)
```

### 2. Type Mismatch

```bend
# Error: Expected Nat, got U64
def bad_example(n: U64) -> Nat:
  n + 1n  # Cannot add U64 and Nat

# Fix: Use consistent types
def good_example(n: Nat) -> Nat:
  n + 1n
```

### 3. Index Mismatch

```bend
# Error: Length mismatch
def bad_vec() -> Vec<Nat, 3n>:
  @Cons{1n, 42n, @Cons{0n, 24n, @Nil{{==}}, {==}}, {==}}  # Only length 2

# Fix: Correct the length
def good_vec() -> Vec<Nat, 2n>:
  @Cons{1n, 42n, @Cons{0n, 24n, @Nil{{==}}, {==}}, {==}}
```

### 4. Impossible Patterns

```bend
# Error: Pattern doesn't type-check
def bad_head<A>(v: Vec<A, 0n>) -> A:
  match v:
    case @Cons{n, h, t, e}:  # Impossible: 0n cannot equal 1n + n
      h

# Fix: Handle the impossible case
def safe_head<A>(v: Vec<A, 0n>) -> Maybe<A>:
  match v:
    case @Nil{e}:
      @None{}  # This is the only possible case
```

## Best Practices

1. **Use dependent types for precision**: Express invariants in types when possible
2. **Keep proofs simple**: Use `{==}` and `rewrite` for most equality proofs
3. **Factor out common patterns**: Create helper lemmas for reused proof patterns
4. **Use holes during development**: Use `()` to see what type is expected
5. **Test with assertions**: Use `assert` to check your understanding

## Further Reading

- [Inductive Types Guide](inductive-types.md) - Deep dive into data type definitions
- [Proof Techniques](proofs.md) - Strategies for writing proofs
- [Examples](examples.md) - Complete programs using the type system
- [Error Guide](errors.md) - Common type errors and their solutions
