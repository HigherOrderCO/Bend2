# Bend Errors and Troubleshooting Guide

This guide helps you understand and fix common errors you might encounter when writing Bend programs.

## Table of Contents

- [Type Errors](#type-errors)
- [Parse Errors](#parse-errors)
- [Pattern Matching Errors](#pattern-matching-errors)
- [Proof Errors](#proof-errors)
- [Runtime Errors](#runtime-errors)
- [Common Pitfalls](#common-pitfalls) 
- [Debugging Strategies](#debugging-strategies)

## Type Errors

### 1. Cannot Infer Type Parameters

**Error Message:**
```
Cannot infer type parameters for polymorphic function
```

**Example:**
```bend
def example() -> Nat[]:
  map(double, [1n, 2n, 3n])  # Error: missing type parameters
```

**Solution:**
```bend
def example() -> Nat[]:
  map<Nat, Nat>(double, [1n, 2n, 3n])  # Explicit type parameters
```

**Why:** Bend has no type inference. All polymorphic applications must be explicit.

### 2. Type Mismatch

**Error Message:**
```
Type mismatch:
- Expected: Nat
- Found: U64
```

**Example:**
```bend
def add_mixed(a: Nat, b: U64) -> Nat:
  a + b  # Error: cannot add Nat and U64
```

**Solution:**
```bend
# Option 1: Use consistent types
def add_nats(a: Nat, b: Nat) -> Nat:
  a + b

# Option 2: Convert between types (if conversion functions exist)
def add_with_conversion(a: Nat, b: U64) -> Nat:
  a + nat_from_u64(b)
```

### 3. Constructor Arity Mismatch

**Error Message:**
```
Constructor @Some expects 1 field, but got 2
```

**Example:**
```bend
type Maybe<A: Set>:
  case @None:
  case @Some:
    value: A

def bad_constructor() -> Maybe<Nat>:
  @Some{1n, 2n}  # Error: @Some only has one field
```

**Solution:**
```bend
def good_constructor() -> Maybe<Nat>:
  @Some{1n}  # Correct: one field

# Or for multiple values, use a tuple
def tuple_constructor() -> Maybe<(Nat, Nat)>:
  @Some{(1n, 2n)}
```

### 4. Index Type Mismatch

**Error Message:**
```
Type mismatch in vector length:
- Expected: Vec<Nat, 3n>
- Found: Vec<Nat, 2n>
```

**Example:**
```bend
def wrong_length() -> Vec<Nat, 3n>:
  @Cons{1n, 42n, @Cons{0n, 24n, @Nil{{==}}, {==}}, {==}}  # Only length 2
```

**Solution:**
```bend
# Option 1: Fix the return type
def correct_length() -> Vec<Nat, 2n>:
  @Cons{1n, 42n, @Cons{0n, 24n, @Nil{{==}}, {==}}, {==}}

# Option 2: Add another element
def correct_length_3() -> Vec<Nat, 3n>:
  @Cons{2n, 1n, @Cons{1n, 42n, @Cons{0n, 24n, @Nil{{==}}, {==}}, {==}}, {==}}
```

### 5. Undefined Variable

**Error Message:**
```
Undefined variable: 'unknown_function'
```

**Example:**
```bend
def example() -> Nat:
  unknown_function(42n)  # Error: function not defined
```

**Solution:**
```bend
# Define the function first
def helper_function(x: Nat) -> Nat:
  x + 1n

def example() -> Nat:
  helper_function(42n)
```

## Parse Errors

### 1. Unexpected Token

**Error Message:**
```
Parse error: unexpected token '}'
Expected: expression
```

**Example:**
```bend
def broken_syntax() -> Nat:
  match 5n
    case 0n:  # Missing colon
      0n
    case _:
      1n
```

**Solution:**
```bend
def correct_syntax() -> Nat:
  match 5n:  # Added colon
    case 0n:
      0n
    case _:
      1n
```

### 2. Indentation Error

**Error Message:**
```
Parse error: inconsistent indentation
```

**Example:**
```bend
def indentation_problem() -> Nat:
  if True:
    1n
  else:
  2n  # Error: incorrect indentation
```

**Solution:**
```bend
def correct_indentation() -> Nat:
  if True:
    1n
  else:
    2n  # Proper indentation
```

### 3. Missing Type Annotation

**Error Message:**
```
Parse error: function definition requires type annotation
```

**Example:**
```bend
def no_types(x):  # Error: missing type annotations
  x + 1n
```

**Solution:**
```bend
def with_types(x: Nat) -> Nat:
  x + 1n
```

## Pattern Matching Errors

### 1. Non-Exhaustive Patterns

**Error Message:**
```
Pattern match is not exhaustive
Missing cases: @None{}
```

**Example:**
```bend
def partial_match(opt: Maybe<Nat>) -> Nat:
  match opt:
    case @Some{x}:
      x
    # Missing @None case
```

**Solution:**
```bend
def complete_match(opt: Maybe<Nat>) -> Nat:
  match opt:
    case @Some{x}:
      x
    case @None{}:
      0n  # Handle the missing case
```

### 2. Impossible Pattern

**Error Message:**
```
Pattern match error: impossible case
Cannot match @Cons on Vec<A, 0n>
```

**Example:**
```bend
def impossible_case<A>(v: Vec<A, 0n>) -> A:
  match v:
    case @Cons{n, h, t, e}:  # Impossible: empty vector can't be cons
      h
```

**Solution:**
```bend
def handle_empty<A>(v: Vec<A, 0n>) -> Maybe<A>:
  match v:
    case @Nil{e}:  # Only possible case
      @None{}

# Or use absurd for truly impossible cases
def with_absurd<A>(v: Vec<A, 0n>) -> A:
  match v:
    case @Nil{e}:
      absurd e  # If we know this case shouldn't happen
```

### 3. Pattern Variable Conflicts

**Error Message:**
```
Pattern error: variable 'x' is bound multiple times
```

**Example:**
```bend
def duplicate_bindings(pair: (Nat, Nat)) -> Nat:
  match pair:
    case (x, x):  # Error: x bound twice
      x
```

**Solution:**
```bend
def unique_bindings(pair: (Nat, Nat)) -> Nat:
  match pair:
    case (x, y):  # Use different variable names
      x + y
```

## Proof Errors

### 1. Failed Rewrite

**Error Message:**
```
Rewrite failed: cannot unify
- Goal: Nat{a + b == c}  
- Proof: Nat{b + a == c}
```

**Example:**
```bend
def bad_rewrite(a: Nat, b: Nat, c: Nat, p: Nat{b + a == c}) -> Nat{a + b == c}:
  rewrite p  # Error: doesn't match the goal exactly
  {==}
```

**Solution:**
```bend
def good_rewrite(a: Nat, b: Nat, c: Nat, p: Nat{b + a == c}) -> Nat{a + b == c}:
  rewrite add_comm(a, b)  # First show a + b == b + a
  rewrite p               # Then use the given proof
  {==}

# Need the commutativity lemma
def add_comm(a: Nat, b: Nat) -> Nat{a + b == b + a}:
  # Implementation omitted
  ()
```

### 2. Equality Mismatch

**Error Message:**
```
Type error in equality:
- Expected: Nat{x == y}
- Found: Nat{y == x}
```

**Example:**
```bend
def wrong_direction(x: Nat, y: Nat, p: Nat{y == x}) -> Nat{x == y}:
  p  # Error: wrong direction
```

**Solution:**
```bend
def fix_direction(x: Nat, y: Nat, p: Nat{y == x}) -> Nat{x == y}:
  rewrite p
  {==}

# Or use symmetry explicitly
def with_symmetry(x: Nat, y: Nat, p: Nat{y == x}) -> Nat{x == y}:
  symmetry(p)
```

### 3. Proof Obligation Not Met

**Error Message:**
```
Failed to prove: Nat{n > 0n}
In context: n : Nat
```

**Example:**
```bend
def unsafe_pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n  # Should be impossible if n > 0
    case 1n + p:
      p
```

**Solution:**
```bend
# Option 1: Add precondition
def safe_pred(n: Nat, proof: Nat{n > 0n}) -> Nat:
  match n:
    case 0n:
      absurd proof  # Use proof to show impossibility
    case 1n + p:
      p

# Option 2: Return Maybe
def maybe_pred(n: Nat) -> Maybe<Nat>:
  match n:
    case 0n:
      @None{}
    case 1n + p:
      @Some{p}
```

## Runtime Errors

### 1. Match Error

**Error Message:**
```
Runtime error: pattern match failure
No matching case for value: @Unknown{}
```

**Example:**
```bend
type Color:
  case @Red:
  case @Blue:
  case @Green:

def describe_color(c: Color) -> String:
  match c:
    case @Red:
      "red"
    case @Blue:
      "blue"
    # Missing @Green case - could cause runtime error
```

**Solution:**
```bend
def describe_color(c: Color) -> String:
  match c:
    case @Red:
      "red"
    case @Blue:
      "blue"
    case @Green:
      "green"  # Handle all cases
```

### 2. Stack Overflow

**Error Message:**
```
Stack overflow in recursive function
```

**Example:**
```bend
def infinite_loop(n: Nat) -> Nat:
  infinite_loop(n)  # No base case
```

**Solution:**
```bend
def finite_recursion(n: Nat) -> Nat:
  match n:
    case 0n:
      0n  # Base case
    case 1n + p:
      1n + finite_recursion(p)  # Structural recursion
```

## Common Pitfalls

### 1. Forgetting Type Parameters

```bend
# Wrong: missing type parameters
def wrong() -> Nat[]:
  map(double, [1n, 2n, 3n])

# Correct: explicit type parameters  
def correct() -> Nat[]:
  map<Nat, Nat>(double, [1n, 2n, 3n])
```

### 2. Mixing Numeric Types

```bend
# Wrong: mixing Nat and U64
def mixed_types(n: Nat) -> U64:
  n + 1  # Error: 1 is U64, n is Nat

# Correct: consistent types
def consistent_types(n: Nat) -> Nat:
  n + 1n  # Both are Nat
```

### 3. Incorrect Pattern Order

```bend
# Wrong: catch-all pattern first
def bad_order(n: Nat) -> String:
  match n:
    case _:        # This catches everything
      "any"
    case 0n:       # Never reached
      "zero"

# Correct: specific patterns first
def good_order(n: Nat) -> String:
  match n:
    case 0n:       # Specific case first
      "zero"
    case _:        # Catch-all last
      "other"
```

### 4. Forgetting Return in Functions

```bend
# Wrong: missing return in some branches
def incomplete_function(b: Bool) -> Nat:
  if b:
    5n
  # Missing else case

# Correct: all branches return
def complete_function(b: Bool) -> Nat:
  if b:
    5n
  else:
    0n
```

## Debugging Strategies

### 1. Use Holes to See Expected Types

```bend
def debug_types(x: Nat, y: Bool) -> String:
  # Use () as a hole to see what type is expected
  ()  # Bend will tell you: Expected String, Found Unit
```

### 2. Add Type Annotations

```bend
# Add explicit type annotations to catch errors early
def with_annotations(x: Nat) -> Nat:
  intermediate : Nat = x + 1n  # Make intermediate types explicit
  result : Nat = intermediate * 2n
  result
```

### 3. Test with Simple Cases

```bend
def test_function(n: Nat) -> Nat:
  # Test with simple inputs using assertions
  assert 1n == test_function(0n) : Nat
  assert 3n == test_function(1n) : Nat
  
  match n:
    case 0n:
      1n
    case 1n + p:
      2n + test_function(p)
```

### 4. Break Down Complex Expressions

```bend
# Instead of one complex expression
def complex_expression(xs: Nat[]) -> Nat:
  fold<Nat, Nat>(add, 0n, map<Nat, Nat>(mul(2n), filter<Nat>(is_even, xs)))

# Break it down step by step
def step_by_step(xs: Nat[]) -> Nat:
  evens : Nat[] = filter<Nat>(is_even, xs)
  doubled : Nat[] = map<Nat, Nat>(mul(2n), evens)
  result : Nat = fold<Nat, Nat>(add, 0n, doubled)
  result
```

### 5. Use the Error Messages

Bend's error messages are quite helpful:
- They show the expected vs actual types
- They indicate the location of the error
- They often suggest what went wrong

### 6. Check for Termination

Make sure recursive functions have proper base cases:

```bend
# Bad: no base case
def bad_recursion(n: Nat) -> Nat:
  1n + bad_recursion(n)

# Good: structural recursion with base case
def good_recursion(n: Nat) -> Nat:
  match n:
    case 0n:
      0n  # Base case
    case 1n + p:
      1n + good_recursion(p)  # Recursive call on smaller input
```

## Getting Help

When you encounter an error:

1. **Read the error message carefully** - Bend's errors are usually informative
2. **Check the syntax reference** - Make sure you're using correct syntax
3. **Look at similar examples** - Find working code that does something similar  
4. **Use holes (`()`)** to explore types interactively
5. **Simplify the problem** - Create a minimal example that reproduces the error

Remember: Type errors are caught at compile time, which means your programs are safer once they type-check successfully!