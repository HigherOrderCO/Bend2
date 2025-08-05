# Bend Documentation

Welcome to the comprehensive documentation for the Bend programming language. Bend is a functional programming language with Python-inspired syntax, Haskell-like semantics, and a powerful dependent type system for formal verification.

## 🚀 Quick Start

1. **[Getting Started](getting-started.md)** - Your first Bend programs and basic concepts
2. **[Syntax Reference](syntax-reference.md)** - Complete syntax guide with examples  
3. **[Examples](examples.md)** - Practical code examples from simple to advanced

## 📚 Core Documentation

### Language Fundamentals
- **[Syntax Reference](syntax-reference.md)** - Complete syntax guide
- **[Type System](type-system.md)** - Dependent types, equality types, and type inference
- **[Inductive Data Types](inductive-datatypes.md)** - Understanding Bend's encoding of inductive types

### Programming Guides
- **[Getting Started](getting-started.md)** - Tutorial for beginners
- **[Examples](examples.md)** - Code examples and patterns  
- **[Advanced Features](advanced-features.md)** - Lambda matching, superposition, meta-programming
- **[Errors and Troubleshooting](errors-and-troubleshooting.md)** - Common errors and how to fix them

## 🎯 Language Overview

Bend combines the best aspects of different programming paradigms:

### Python-Inspired Syntax
```bend
def fibonacci(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n:
      1n
    case 2n + p:
      fibonacci(1n + p) + fibonacci(p)
```

### Dependent Types
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
```

### Formal Verification
```bend
# Prove that addition is commutative
def add_comm(a: Nat, b: Nat) -> Nat{add(a, b) == add(b, a)}:
  match a:
    case 0n:
      add_zero_right(b)
    case 1n + p:
      ih = add_comm(p, b)
      rewrite ih
      rewrite add_succ_right(b, p)
      {==}
```

## 🔧 Key Features

- **No Type Inference**: All types must be explicit, making code predictable and readable
- **Dependent Types**: Express precise specifications and verify them at compile time
- **Pattern Matching**: Comprehensive pattern matching on data structures
- **Proof Assistant**: Write mathematical proofs alongside your programs
- **Automatic Imports**: Import system based on usage patterns
- **Lambda Matching**: Advanced pattern matching with lambda expressions

## 📖 Documentation Structure

### For Beginners
1. Start with **[Getting Started](getting-started.md)** for a gentle introduction
2. Read **[Syntax Reference](syntax-reference.md)** for complete syntax
3. Try examples from **[Examples](examples.md)**
4. Consult **[Errors and Troubleshooting](errors-and-troubleshooting.md)** when stuck

### For Advanced Users
1. **[Type System](type-system.md)** - Deep dive into dependent types
2. **[Advanced Features](advanced-features.md)** - Lambda matching, superposition, meta-programming
3. **[Inductive Data Types](inductive-datatypes.md)** - Understanding the encoding

### For Researchers
1. **[Type System](type-system.md)** - Formal type theory foundations
2. **[Inductive Data Types](inductive-datatypes.md)** - "Fording" encoding technique
3. **[Advanced Features](advanced-features.md)** - Meta-programming and proof techniques

## 🌟 What Makes Bend Unique

### 1. Explicit Everything
Unlike most languages, Bend requires explicit type parameters:
```bend
# Must be explicit
map<Nat, Nat>(double, [1n, 2n, 3n])

# This would be an error
map(double, [1n, 2n, 3n])
```

### 2. Proofs as Programs
Mathematical proofs are first-class values:
```bend
# This is both a function and a proof
def double_neg(b: Bool) -> Bool{not(not(b)) == b}:
  match b:
    case True: {==}
    case False: {==}
```

### 3. Inductive Types via "Fording"
Instead of built-in inductive types, Bend encodes them using dependent pairs and enums:
```bend
# This generates the appropriate encoding automatically
type List<A: Set>:
  case @Nil:
  case @Cons:
    head: A
    tail: List<A>
```

### 4. Lambda Matching
Pattern match directly in lambda expressions:
```bend
# Boolean eliminator  
λ{False: "no"; True: "yes"}

# List fold using lambda matching
λ{[]: 0n; <>: λh t. 1n + t}
```

## 🎨 Common Patterns

### Safe Programming
```bend
# Use Maybe for nullable values
def safe_head<A>(xs: A[]) -> Maybe<A>:
  match xs:
    case []: @None{}
    case h <> _: @Some{h}

# Use dependent types for array bounds
def safe_get<A>(n: Nat, i: Nat, arr: Vec<A, n>, proof: Nat{i < n}) -> A:
  # Implementation guarantees no bounds errors
  vec_get<A>(i, arr)
```

### Verification
```bend
# Express and verify properties
def sorted_insert(x: Nat, xs: Nat[], proof: Nat{is_sorted(xs) == True}) -> 
  any ys:Nat[]. Nat{is_sorted(ys) == True}:
  # Implementation preserves sortedness
  (insert(x, xs), insert_preserves_sorted(x, xs, proof))
```

## 🔗 Related Resources

- **Original Bend Project**: [Higher-Order Co Bend](https://github.com/HigherOrderCO/Bend)
- **WanShi Repository**: [Example Bend Programs](https://github.com/HigherOrderCO/WanShi)
- **HVM**: [High-order Virtual Machine](https://github.com/HigherOrderCO/HVM) (Bend's runtime)

## 📝 Contributing to Documentation

This documentation is designed to be comprehensive and accessible. If you find errors, have suggestions, or want to contribute examples:

1. The documentation lives in the `docs/` directory
2. Each file is written in Markdown
3. Examples should be tested with `bend filename.bend`
4. Follow the existing style and structure

## 🚀 Getting Help

- **Start Here**: [Getting Started Guide](getting-started.md)
- **Syntax Questions**: [Syntax Reference](syntax-reference.md)  
- **Type Errors**: [Errors and Troubleshooting](errors-and-troubleshooting.md)
- **Examples**: [Examples Collection](examples.md)
- **Advanced Topics**: [Advanced Features](advanced-features.md)

---

*Bend: Where functional programming meets formal verification with Python-like syntax.*