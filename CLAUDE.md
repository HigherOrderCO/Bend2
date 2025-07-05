# Bend2

This repository implements the Bend2 language.

It is structured as follows:

- bend.cabal: the cabal file. Bend doesn't use stack.
  - Build this project with `cabal build`.
  - Run with `cabal run bend file.bend`.

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
