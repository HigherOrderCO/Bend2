
# Import System

This document aims to describe the import system specification in the Bend programming language.

Bend aims to be a programming language AI-directed. This means AI's should handle the files and the code the most optimal way possible. Imports are a big part of this when working on big codebases without wasting context.

The smallest part of a `Bend` codebase is a **definition**. Definitions are introduced by `def name()...`. Those definitions are in files that live in a specific path.

All definitions, along with their paths, build up a **Fully Qualified Name**, which will be called FQN across this document.

So for example, a function in: `./Nat/operations.bend`, defined as `def add...` will have the FQN: `Nat/operations::add` . Note that `/` denotes the filepath of the functions, whereas `::` denotes the function name that lives there.

This creates a very interesting and important property in our system. All functions are **UNIQUELY** defined by their FQN, and there is only ONE definition per FQN. This creates a 1 : 1 mapping, where knowing the FQN of some definition, we **must** know exactly where it lives. This is extremely good for AI contexts, since now it does not have to keep `import` syntaxes or other context bloat.

Also, this way we're able to build an import system based on this basic blocks, where we DO NOT BRING ANY USELESS DEFINITION TO SCOPE.

This means we absolutely **not** import entire modules, such as `import Nat` bringing `Nat/operations.bend`, `Nat/proofs.bend` or other files into scope. The definitions into scope are strictly the ones used in the code.

So, in my code, I should be able to write `def main() -> Nat: Nat/some_file/some_other_file::definition()` and this should only bring that specific definition (and it's dependencies, obviously individually as well) into scope. 

The only syntax sugar we should have available is to allow *aliases* to be created. This syntax should be: `import FQN as alias`, and the implementation should be a simple substitution map where alias point to the correct FQN. Note that aliases go up to paths, so you do: `import Nat/some_file/some_other_file as F` and then do `F::definition()`. 

Now, Bend also has an external import system, that is a package index. This package is a global tree of all definitions.

It should be a stateful, global, stored in Bend's server, and it is a tree of bend file → contents and a Bend directory should necessarily be a view of the global tree, with matching paths so, if you're working on your TODO app, you'd have something like `BendRoot/@lorenzo/todo_app/main.bend` and, if main.bend uses other stuff, it will be downloaded below BendRoot just like they are on the remote server.

Ex:
```
BendRoot/@lorenzo/todo_app/main.bend
BendRoot/Nat/add.bend
BendRoot/List/add.bend
... etc ...
```

your local BendRoot dir is a subset of the global directory, and files are downloaded as you use definitions
now, when you change something, you're temporarily out of sync with the global repo
so, when importing, Bend does this:

- attempt to load from the local BendRoot
- if it isn't there, download from the BendRoot server
- attempt to load from the local BendRoot (will be available now)

that's all - simple as this. nothing else will be supported
then, to publish, you just do:

`bend publish`

and it will upload all your local files to the BendRoot server, and overwrite.

Of course, here we check permissions: if I change `BendRoot/Nat/add.bend`, then bend publish will fail, because I don't have permission to mutate `BendRoot/Nat/add.bend`

Obviously this also involves the package index repository, so now we're focusing on the Bend specification.

For Bend, we must guarantee that the imports fall back to the package index API if we don't find them locally.

### Versioning

Bend uses a package-based versioning system that balances user ergonomics with the core principle of individually addressable definitions.

**Package Version Syntax**

The version number appears at the package level, not per-definition:
```
import VictorTaelin/VecAlg#7/List/dot as dot
```

This groups related definitions (add, sub, mul, etc.) under a single version, preventing the chaotic scenario where each function has independent versions that may be incompatible when used together.

**Key Properties**

1. **Package-level versioning**: Version `#7` applies to all definitions within `VictorTaelin/VecAlg`, ensuring coherent sets of functions that are tested and published together.

2. **Individual addressability**: Internally, each definition remains fully independent. The resolver and database treat `VictorTaelin/VecAlg#7/List/dot` as a unique FQN, enabling minimal context loading—only the specific definitions used (plus their dependencies) are pulled into scope.

3. **Direct reference capability**: Any definition can be referenced anywhere using its full FQN without explicitly importing the package first, maintaining context efficiency.

**Implementation Notes**

- When publishing via `bend publish`, definitions are grouped into packages with a single version identifier
- The package index stores definitions independently but associates them with package metadata for user-facing operations
- Tree-shaking is automatic: importing one function from a package never forces loading the entire package—only the transitive closure of that function's dependencies
- This avoids the npm problem where using a single helper function requires downloading entire libraries

**Storage Format**

Package versions are stored in the global tree with paths like:
```
BendRoot/@VictorTaelin/VecAlg#7/List/dot.bend
BendRoot/@VictorTaelin/VecAlg#7/Nat/add.bend
```

The resolver treats the version as part of the path structure, ensuring different versions can coexist in the dependency tree when needed.

Importing / using `BendRoot/@VictorTaelin/VecAlg/List/dot::fn()` will error out. A version NEEDS to be specified.

In terms of storing, we will always store different versions in different places, meaning:

```
@lorenzo/my_app#0
# contains:
@lorenzo/my_app#0/main::foo()
@lorenzo/my_app#0/main::bar()
```

Then, this get stored in the BendRoot index in that exact structure.

Then, I decide to update only the foo() implementation.
So, the package needs to be updated.
Therefore, we now have to create:

```
@lorenzo/my_app#1
# contains:
@lorenzo/my_app#1/main::foo() -> changed
@lorenzo/my_app#1/main::bar() -> didnt change
```

Note that we're storing bar() twice even though the implementations are identical, but this is the CORRECT way to do so.

## Current Implementation Overview

### Parser and Surface Syntax

- The only recognised import form is `import <target> as <alias>`.
- `<target>` is parsed as a POSIX-style path with an optional `::constructor` suffix. Examples:
  - `Nat/add` (brings the file `Nat/add.bend` into scope, i.e just adds it at the substitution map, do not bring all definitions)
  - `Nat/add::add` (directly references the `add` definition inside that file)
  - `Nat/list` (creates a prefix alias; every later reference `Nat` resolves under the original path)
- Aliases are stored as `ImportAlias` records in the `ParserState` and later consumed by the resolver—there is no textual rewriting at parse time anymore.
- Paths that contain package versions (for example `@lorenzo/my_app#1/...`) are accepted verbatim by the parser; the `#` segment is treated as just another path component. There is currently no parser-level enforcement that a version segment actually exists—validation must happen downstream.
- Legacy constructs (`from ... import ...`, implicit module imports, slash aliases, etc.) have been removed; code using them will now fail during parsing.

### Resolver Pipeline

All resolution happens inside `Core.Import`. The high-level flow for `autoImportWithExplicit` is:

1. **BendRoot Enforcement**
   - `ensureBendRoot` checks that the CLI is executed from a directory named `BendRoot/`.
   - `normalizeRelativePath` guarantees that the processed file lives under BendRoot; otherwise an error is raised immediately.

2. **Substitution Maps**
   - `buildAliasSubstMap` turns parsed `ImportAlias` entries into two mappings:
     - Prefix aliases (`alias -> target::prefix`) so expressions like `F::foo` rewrite back to the fully qualified name.
     - Direct function aliases (`alias -> FQN`) when the import target itself already includes `::`.
   - `buildLocalSubstMap` scans the local book (produced by parsing the current file) and registers short names for functions and constructors defined in that file.
   - Substitution maps are purely textual rewrites: they only affect names inside already loaded terms and never trigger IO.

3. **Dependency Closure**
   - The base book is rewritten using alias+local substitutions and its dependencies are collected via `Core.Deps.getBookDeps`.
   - An import loop (`resolveAll`) repeatedly dequeues unmet dependencies:
     - If a dependency already exists in the current book (or has been loaded), nothing happens.
     - Otherwise, the system splits the FQN into `(path, defName)` and calls `loadModule path`.

4. **Module Loading**
   - `loadModule` tries to read `path.bend` or `path/_.bend` relative to BendRoot.
   - If neither exists, the resolver asks the package index to download the missing files (see Package Index Integration below) and retries.
   - The module is parsed, its own alias map plus local substitutions are applied, and the file is cached in-memory so repeated dependencies don’t re-parse the same file.
   - Only the specific definition requested by the dependency is inserted into the final book; the rest of the module remains dormant unless referenced later.
   - Any new dependencies discovered inside that definition are pushed onto the pending set and processed in the same way. This guarantees that exactly the transitive closure of referenced definitions is loaded—never the entire module.

5. **Constructors and Enums**
   - When `buildLocalSubstMap` visits a definition, it inspects its body/type for `Enu` tags and records both fully qualified constructor names and unqualified ones. This enables enum constructors such as `WLeaf` to be rewritten to `examples/main::WTreeTag::WLeaf`, preserving uniqueness.
   - Alias substitutions respect enum names as well, so `import Foo/bar as B` allows references like `B::Type::Ctor`.

### Package Index Integration

- The helper module `Package.Index` now exposes:
  - `IndexConfig { apiBaseUrl, bendRootDir }`
  - `defaultIndexConfig :: FilePath -> IO IndexConfig`
  - `ensureFile :: IndexConfig -> FilePath -> IO (Either String ())`
- Whenever the resolver cannot find a `.bend` file locally, it calls `ensureFile` with the POSIX path (e.g. `Nat/add.bend` or `Nat/add/_.bend`).
  - If the file is already present under BendRoot, the function is a no-op.
  - Otherwise, a GET request is issued to `apiBaseUrl ++ "/api/files/" ++ <posix-path>`; on success, the response body is written under the corresponding BendRoot path, creating directories as needed.
  - Any network failure emits a warning and the resolver continues trying other candidates (e.g. the `_.bend` variant). A fatal error is raised only after all candidates and downloads fail.
- The resolver always works with BendRoot-relative POSIX paths, so the local directory structure mirrors the remote package tree exactly, matching the spec. Version identifiers (the `#N` segments) are carried through untouched and therefore become literal directory names.

### Effects on Files and Definitions

- Every Bend source file is expected to live under `BendRoot/<path>.bend` or `BendRoot/<path>/_.bend`.
- Parsing a file never loads dependencies automatically; all extra files are fetched lazily as dependencies are discovered during resolution.
- Books produced by the resolver only contain definitions that were directly requested by user code (plus their dependencies). This keeps the global scope clean and prevents accidental name clashes.
- If multiple modules define constructors with the same short name, the enum substitution map keeps both their fully qualified names, and the unqualified alias is dropped when ambiguous.

### Practical Notes

- CLI scripts, tests, and external tooling must change directories to BendRoot before invoking `bend` or using the parsing APIs that call `autoImport`.
- Because alias substitution is purely syntactic, referencing an alias that never maps to a real definition will surface as an unresolved dependency during the import loop, making it easier to diagnose missing files instead of silently rewriting to incorrect paths.
- The resolver caches parsed modules within a single import run, but it does not persist results between CLI invocations; subsequent runs will re-read files from disk (which should be in sync thanks to BendRoot mirroring).
- The package index client currently assumes a `GET /api/files/<path>` endpoint that responds with raw Bend source. Future enhancements (permissions, authentication) can extend the helper without touching the resolver core.

Together, these pieces implement the spec’s core principles: every definition is addressed by an FQN, imports introduce no unwanted names, aliases act as predictable textual sugar, and the package index is transparently consulted whenever the local BendRoot is missing a required file.

### Spec Compliance Gaps

- The resolver does not yet reject imports that omit an explicit package version (e.g. `BendRoot/Nat/add.bend` is still accepted when present locally). The specification requires every external reference to include a `#<version>` segment, so an additional validation pass is needed before module loading to enforce this rule consistently.
