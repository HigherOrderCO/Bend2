# Proof Synthesis Pipeline

This note documents how Bend's `gen` blocks are expanded into concrete
definitions.  It complements the high-level overview in `docs/pretty.md` and
focuses on the full end-to-end pipeline implemented inside `src/Core/Gen.hs`,
`src/Target/HVM`, and the CLI.

## 1. Authoring `gen` Blocks

The front-end accepts a `def`-like declaration preceded by the `gen` keyword:

```bend
gen mul2(n: Nat) -> Nat

assert mul2(2n) == 4n : Nat
assert mul2(3n) == 6n : Nat
```

- The parser (`src/Core/Parse/Book.hs`) turns the declaration into a metavariable
  term (`Met`) tagged with the original source span.  This span is later used to
  splice the synthesized program back into the file.
- Optional `assert` statements are desugared into ordinary definitions whose
  bodies are proofs of equality.  They are kept in the book so the synthesizer
  can observe the examples.

## 2. CLI Detection and Book Preparation

`Core.CLI.runCLIGo` controls the synthesis flow:

1. The file is parsed and adjusted (`Core.Adjust.Adjust`).
2. `collectGenInfos` scans the adjusted book for `Met` nodes that originate from
   the current file, recording:
   - Fully qualified name and simple name.
   - Original span.
   - Expected type and context (helper functions captured in braces).
3. `bookHasMet` simply checks whether any definition still contains a `Met`.

If `gen` targets exist, the CLI delegates to `generateDefinitions`; otherwise it
proceeds to type-checking or execution.

## 3. Compiling to HVM

`Target.HVM.HVM.compile` converts the entire Bend book into the Kolmo/HVM
intermediate language:

- Definitions are compiled in the order declared by the original book names
  (see `compileBook`).  This ordering is important because it preserves the
  pairing between input `gen`s and the results emitted by the synthesizer.
- Each metavariable is encoded as a generator term (`HGen`), and its Kolmo nick
  (uppercase identifier) is appended to `ctxGens`.
- When at least one generator is present, `@main` is emitted as a list of
  uppercase generator references.  For two goals `f` and `g`, the generated HVM
  code looks like:
  ```
  @MAIN = [@F @G] ;
  ```

## 4. Running the Synthesizer (`hvm4`)

`Core.Gen.generateDefinitions` writes the HVM program to a temporary file and
spawns:

```
hvm4 <temp-file> -C1
```

- A 5-second timeout guards against runaway synthesis.
- Non-empty stderr or non-zero exit codes are surfaced as Bend errors.

The stdout payload contains one or more HVM lambda terms that implement the
requested functions.

## 5. Parsing the Synthesizer Output

`Target.HVM.Parse.parseGeneratedTerms` handles the raw output:

- Single-term payloads (legacy behaviour) parse directly as a `HCore`.
- Multi-goal payloads are bracketed lists `[term0, term1, …]`. Each item is
  parsed independently, producing an ordered `[HCore]`.

Because compilation and collection both respect the book order, entries in this
list align index-for-index with the corresponding `GenInfo`.

## 6. Prettifying the Results

Each `HCore` is converted into a Bend definition via
`Target.HVM.Pretty.prettyGenerated`:

- The function signature is reconstructed from the recorded type.
- Helper lambdas captured in the generator context are stripped.
- The body is pretty-printed into proper case-tree form as described in
  `docs/pretty.md`.

Failures at this stage bubble up as user-facing errors that include the
simplified name of the definition being prettified.

## 7. Rewriting the Source File

`applyGenerated` attaches the pretty-printed text back into the original file:

- For each `GenInfo`, lookup the synthesized text by simple name.
- Use the stored `Span` to replace the range that contained the `gen`
  declaration.
- Rewrites are applied back-to-front to preserve earlier offsets.
- The updated contents are written to the same file, so subsequent CLI runs see
  real `def` blocks instead of metas.

## 8. Error Handling Highlights

- Missing or extra generated definitions produce descriptive count mismatches.
- Timeout or stderr noise from `hvm4` short-circuit the pipeline.
- Metavariables remaining after generation (e.g., because synthesis failed) are
  reported by the CLI with guidance to run `bend verify`.

## 9. Testing Support

The test harness in `test/Test.hs` allows integration-style tests.  For example,
`test/tests/check_gen_multi.hs` exercises two concurrent goals and asserts that
the CLI synthesizes both before execution.  Tests use `runhaskell -i:test …`
which routes through `cabal run bend` automatically, so they exercise the same
pipeline as the CLI.

## 10. Summary of Key Modules

| Responsibility           | Module / Function                                    |
| ------------------------ | ---------------------------------------------------- |
| Detect metas, gather spans | `Core.Gen.collectGenInfos`                         |
| Compile Bend book to HVM | `Target.HVM.HVM.compile` / `compileBook`             |
| Run external synthesizer | `Core.Gen.generateDefinitions`                       |
| Parse HVM output         | `Target.HVM.Parse.parseGeneratedTerms`               |
| Pretty-print to Bend     | `Target.HVM.Pretty.prettyGenerated`                  |
| Rewrite source file      | `Core.Gen.applyGenerated`                            |

With this pipeline, `gen` blocks behave like source-level holes: they are
compiled into synthesizer tasks, evaluated externally, and finally rewritten as
ordinary Bend functions that the rest of the toolchain can type-check and run.
