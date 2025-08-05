# Getting Started with Bend

Welcome to Bend, a functional programming language that combines Python-like syntax with dependent types and formal verification capabilities. This guide will help you write your first Bend programs.

## Prerequisites

Make sure you have Bend installed and can run:
```bash
bend --help
```

## Your First Bend Program

Let's start with a simple "Hello, World!" program:

```bend
# hello.bend
def main() -> String:
  "Hello, World!"
```

Run it with:
```bash
bend hello.bend
```

## Basic Concepts

### 1. Functions and Types

Bend is a strongly typed language. Every function must have a type signature:

```bend
# Simple function
def double(x: Nat) -> Nat:
  x + x

# Test it
assert 6n == double(3n) : Nat
```

### 2. Natural Numbers

Bend has built-in natural numbers with pattern matching:

```bend
def factorial(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n + p:
      n * factorial(p)

assert 24n == factorial(4n) : Nat
```

### 3. Lists

Lists are fundamental data structures in Bend:

```bend
def length<A>(xs: A[]) -> Nat:
  match xs:
    case []:
      0n
    case _ <> tail:
      1n + length<A>(tail)

# Test with different types
assert 3n == length<Nat>([1n, 2n, 3n]) : Nat
assert 4n == length<Char>(['a', 'b', 'c', 'd']) : Nat
```

### 4. Custom Data Types

Define your own algebraic data types:

```bend
type Maybe<A: Set>:
  case @None:
  case @Some:
    value: A

def map_maybe<A, B>(f: A -> B, m: Maybe<A>) -> Maybe<B>:
  match m:
    case @None{}:
      @None{}
    case @Some{value}:
      @Some{f(value)}
```

## Working with Proofs

One of Bend's unique features is its ability to express and verify mathematical proofs.

### Equality Proofs

```bend
# Prove that addition is commutative for small numbers
def add_comm_small(a: Nat, b: Nat) -> Nat{add(a, b) == add(b, a)}:
  match a:
    case 0n:
      # Need to prove: add(0n, b) == add(b, 0n)
      # Left side: add(0n, b) = b
      # Right side: add(b, 0n) = b (by add_zero_right)
      rewrite add_zero_right(b)
      {==}
    case 1n + a':
      # Inductive case
      ih = add_comm_small(a', b)  # Induction hypothesis
      # ... proof steps ...
      {==}

# Helper lemma
def add_zero_right(n: Nat) -> Nat{add(n, 0n) == n}:
  match n:
    case 0n:
      {==}
    case 1n + p:
      1n + add_zero_right(p)
```

### Dependent Types

Bend supports dependent types for more precise specifications:

```bend
# Vectors with compile-time length checking
type Vec<A: Set>(N: Nat) -> Set:
  case @Nil:
    e: Nat{N == 0n}
  case @Cons:
    n: Nat
    head: A
    tail: Vec<A, n>
    e: Nat{N == 1n + n}

def vec_head<A>(n: Nat, v: Vec<A, 1n + n>) -> A:
  match v:
    case @Nil{e}:
      # This case is impossible since 1n + n != 0n
      absurd e
    case @Cons{m, head, tail, e}:
      head
```

## Pattern Matching Deep Dive

Pattern matching is central to Bend programming:

### Basic Patterns

```bend
def describe_list<A>(xs: A[]) -> String:
  match xs:
    case []:
      "empty list"
    case [x]:
      "single element"
    case [x, y]:
      "two elements"
    case _ <> _ <> _:
      "three or more elements"
```

### Constructor Patterns

```bend
type Result<T, E: Set>:
  case @Ok:
    value: T
  case @Error:
    error: E

def map_result<A, B, E>(f: A -> B, r: Result<A, E>) -> Result<B, E>:
  match r:
    case @Ok{value}:
      @Ok{f(value)}
    case @Error{error}:
      @Error{error}
```

### Multiple Scrutinees

```bend
def compare_bools(a: Bool, b: Bool) -> String:
  match a b:
    case True True:
      "both true"
    case False False:
      "both false"
    case True False:
      "first true, second false"
    case False True:
      "first false, second true"
```

## Higher-Order Functions

Bend supports higher-order functions naturally:

```bend
def map<A, B>(f: A -> B, xs: A[]) -> B[]:
  match xs:
    case []:
      []
    case h <> t:
      f(h) <> map<A, B>(f, t)

def filter<A>(p: A -> Bool, xs: A[]) -> A[]:
  match xs:
    case []:
      []
    case h <> t:
      if p(h):
        h <> filter<A>(p, t)
      else:
        filter<A>(p, t)

def fold<A, B>(f: A -> B -> B, acc: B, xs: A[]) -> B:
  match xs:
    case []:
      acc
    case h <> t:
      fold<A, B>(f, f(h, acc), t)
```

## Error Handling Patterns

### Using Maybe for Nullable Values

```bend
def safe_head<A>(xs: A[]) -> Maybe<A>:
  match xs:
    case []:
      @None{}
    case h <> _:
      @Some{h}

def safe_tail<A>(xs: A[]) -> Maybe<A[]>:
  match xs:
    case []:
      @None{}
    case _ <> t:
      @Some{t}
```

### Using Result for Error Handling

```bend
def safe_divide(a: Nat, b: Nat) -> Result<Nat, String>:
  match b:
    case 0n:
      @Error{"Division by zero"}
    case _:
      @Ok{a / b}
```

## Working with Strings

Strings in Bend are lists of characters:

```bend
def string_length(s: String) -> Nat:
  length<Char>(s)

def string_reverse(s: String) -> String:
  reverse<Char>(s)

def is_empty_string(s: String) -> Bool:
  match s:
    case []:
      True
    case _:
      False
```

## Numeric Operations

Bend supports various numeric types:

```bend
# Natural numbers (0n, 1n, 2n, ...)
def nat_example(n: Nat) -> Nat:
  n + 5n

# 64-bit unsigned integers (0, 1, 2, ...)
def u64_example(n: U64) -> U64:
  n * 2

# 64-bit signed integers (+0, +1, -1, ...)
def i64_example(n: I64) -> I64:
  n - 10

# 64-bit floating point (0.0, 1.5, -3.14, ...)
def f64_example(x: F64) -> F64:
  x * 2.0 + 1.0
```

## Testing Your Code

Use `assert` statements to test your functions:

```bend
# Test natural number arithmetic
assert 5n == add(2n, 3n) : Nat
assert 6n == mul(2n, 3n) : Nat

# Test list operations
assert 3n == length<Nat>([1n, 2n, 3n]) : Nat
assert [3n, 2n, 1n] == reverse<Nat>([1n, 2n, 3n]) : Nat[]

# Test custom types
assert @Some{42n} == map_maybe<Nat, Nat>(lambda x. x, @Some{42n}) : Maybe<Nat>
```

## Common Patterns and Idioms

### 1. Option/Maybe Pattern

```bend
def unwrap_or<A>(default: A, opt: Maybe<A>) -> A:
  match opt:
    case @None{}:
      default
    case @Some{value}:
      value
```

### 2. List Processing

```bend
def take<A>(n: Nat, xs: A[]) -> A[]:
  match n xs:
    case 0n _:
      []
    case _ []:
      []
    case 1n+m h<>t:
      h <> take<A>(m, t)

def drop<A>(n: Nat, xs: A[]) -> A[]:
  match n xs:
    case 0n xs:
      xs
    case _ []:
      []
    case 1n+m _<>t:
      drop<A>(m, t)
```

### 3. Tree Traversal

```bend
type Tree<A: Set>:
  case @Leaf:
    value: A
  case @Node:
    left: Tree<A>
    right: Tree<A>

def tree_map<A, B>(f: A -> B, tree: Tree<A>) -> Tree<B>:
  match tree:
    case @Leaf{value}:
      @Leaf{f(value)}
    case @Node{left, right}:
      @Node{tree_map<A, B>(f, left), tree_map<A, B>(f, right)}
```

## Next Steps

Now that you understand the basics:

1. **Read the [Syntax Reference](syntax-reference.md)** for complete syntax details
2. **Explore [Type System](type-system.md)** to understand dependent types
3. **Check out [Examples](examples.md)** for more complex programs
4. **Learn about [Proofs](proofs.md)** to verify your programs mathematically

## Common Beginner Mistakes

1. **Forgetting Type Parameters**: Remember to include `<Type>` in polymorphic function calls
   ```bend
   # Wrong
   map(double, [1n, 2n, 3n])
   
   # Correct
   map<Nat, Nat>(double, [1n, 2n, 3n])
   ```

2. **Type Mismatches**: Natural numbers (`1n`) vs integers (`1`) are different types
   ```bend
   # Wrong
   def bad_add(a: Nat, b: U64) -> Nat:
     a + b  # Type error!
   
   # Correct - choose consistent types
   def good_add(a: Nat, b: Nat) -> Nat:
     a + b
   ```

3. **Missing Cases in Pattern Matching**: Ensure all cases are covered
   ```bend
   # Wrong - missing case
   def partial_bool(b: Bool) -> String:
     match b:
       case True:
         "yes"
       # Missing False case!
   
   # Correct
   def complete_bool(b: Bool) -> String:
     match b:
       case True:
         "yes"
       case False:
         "no"
   ```

Happy coding with Bend!