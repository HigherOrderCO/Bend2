# Bend2

This repository implements the Bend2 language.

It is structured as follows:

- bend.cabal: the cabal file. Bend doesn't use stack.
  - Build this project with `cabal build`.
  - Run with `bend file.bend`.
  - When debugging, run with:
    `cabal run -v0 bend --project-dir=PATH_TO_BEND2_DIR -- FILE_NAME OPTIONS`
    This is faster than rebuilding and running.

- src/Core/Type.hs: most important file, always read. Includes every type used in
  this repo, including the Term type for Bend's core language.

- src/Core/WHNF.hs: evaluates a term to weak head normal form. Includes all
  computation rules of the interpreter.

- src/Core/Check.hs: bidirectional type-checker for Bend terms and proofs.

- src/Core/Equal.hs: equality between terms. Used by the checker.

- src/Core/Rewrite.hs: rewrites an expression by another. Used by the checker.

- src/Core/Bind.hs: binds named variables to native λ's (HOAS). Used after parsing.

- src/Core/Flatten.hs: converts generalized pattern-matches to native eliminators
  (case-of). Used after parsing.

- src/Core/Adjust.hs: flattens and binds in topological order. Used after parsing.

- src/Core/CLI.hs: Bend's command-line interface.

- src/Core/Import.hs: auto-import feature. Used by the CLI.

- src/Core/Deps.hs: collects all external dependencies of a term. Used by the CLI.

- src/Core/Parse.hs: parser type, commons and utils (lexeme, keywords, etc.).

- src/Core/Parse/Term.hs: all core term parsers (lambdas, pairs, numbers, etc.).

- src/Core/Parse/Book.hs: top-level persers (def, type, import, etc.).

- src/Core/Parse/WithSpan.hs: temporary hack to improve errors (not important).

- src/Target/JavaScript.hs: compiles Bend files to JavaScript modules.

- app/Main.hs: entry point for the CLI.

- examples/prompt.bend: concise file designed to quickly learn the syntax

- examples/main.bend: many random examples

- docs/syntax.md: longer syntax guide for humans (AIs prefer prompt.bend)

- docs/inductive-datatypes.md: how are inductive types encoded? (A: via "Fording")

## Testing

The Bend2 test framework is located in the `test/` directory:

- test/Main.hs: test runner that finds and executes all test files
- test/Test.hs: testing framework module with assertions and utilities
- test/tests/: directory containing test files
- test/README.md: comprehensive testing documentation

To run tests:
- All tests: `cabal test`
- Single test: `runhaskell -i:test test/tests/BasicTest.hs`

### Test Style Convention

Tests follow a specific format convention:

1. **Test File Naming**: Each test file in `test/tests/` is a unit test
   - Name pattern for type-checking tests: `check_<function_name>.hs` (tests if function checks and computes correctly)
   - Name pattern for error tests: descriptive names like `mismatch_bool_nat.hs`
   - Examples: `check_id.hs`, `check_add.hs`, `mismatch_bool_nat.hs`

2. **Canonical Test File Structure** (for type-checking tests):
```haskell
{-# LANGUAGE MultilineStrings #-}

import Test

-- Each top-level Haskell definition represents a virtual .bend file
-- Convention: use <name>_bend for definitions (e.g., id_bend represents "id.bend")
id_bend :: String
id_bend = """
def id<A>(x: A) -> A:
  x

-- Include inline tests using assert syntax
assert 3n == id<Nat>(3n) : Nat
assert True == id<Bool>(True) : Bool
assert 0n == id<Nat>(id<Nat>(0n)) : Nat
assert "hello" == id<String>("hello") : String
"""

main :: IO ()
main = testFileChecks id_bend
```

3. **Test Functions Available**:
   - `testFileChecks`: Alias for tests that just need to type-check (checks that `err == ""`)
   - `testFile`: Full test function when you need to check stdout/stderr explicitly
   - `testFileGoal`: Test that a file produces a specific goal in the error output
   - `test`: Most general function for testing multiple files

Key conventions:
- Use top-level string definitions for Bend code (not inline strings)
- Name convention: `<name>_bend` represents a virtual `.bend` file within the test
- Include 3-4 inline tests using the `assert` syntax within the Bend code to test the function
- Assert syntax: `assert A == B : T` desugars to `def EN : T{A == B} = {==}` where N is auto-incremented
- A file is considered successfully checked when `err == ""`
- For simple type-checking tests, use `testFileChecks` (canonical style)
- For tests that need to verify specific output or errors, use `testFile`
- For tests that check intermediate goals in proofs, use `testFileGoal`

The framework provides:
- `assert`: basic assertions
- `has`: checks if output contains text (ignores ANSI colors and whitespace)
- Colored output showing test results

### Goal Testing Convention

For proof functions, create additional test files that check intermediate goals:
- Name pattern: `check_<function>_goal_<N>.hs` where N starts from 0
- These tests place `()` holes at different points in the proof
- Use `testFileGoal` to verify the expected goal and context

Example:
```haskell
testFileGoal code "Nat{add(b,c)==add(b,c)}" [("b", "Nat"), ("c", "Nat")]
```

This checks that the goal is `Nat{add(b,c)==add(b,c)}` and that variables `b` and `c` have type `Nat` in the context.
