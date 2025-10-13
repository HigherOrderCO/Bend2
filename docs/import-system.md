# Bend Import System

This document explains how Bend discovers, resolves, and rewrites imports. It follows the code in `src/Core/Import.hs`, `src/Core/Parse`, and the CLI pipeline, so every rule described here reflects the interpreter’s behaviour.

## Overview

Import resolution happens in three stages each time a Bend file is parsed:

1. **Parse time:** `src/Core/Parse/Book.hs` records every `import …` directive in the `ParserState`. Every definition in the file is immediately qualified with the module path derived from the file name.
2. **Explicit imports:** `Core.Import.processExplicitImports` materialises the parsed directives by loading the requested modules (local or external), filtering definitions, and building substitution tables that encode aliases.
3. **Dependency closure:** `Core.Import.importLoop` repeatedly scans the cumulative book for unresolved references, loads missing modules on demand, and applies name substitutions so that every reference becomes a fully qualified name (FQN).

The end result is a single `Book` value where every definition key is a FQN like `examples/prompt::Nat/add`, and every reference inside terms/types is already rewritten to those FQNs.

## Source Syntax

The parser understands the following surface forms (see `parseImport` in `src/Core/Parse/Book.hs`):

- `import Module/path` – load every definition from the module file.
- `import Module/path as Alias` – same as above, but referenced via `Alias::def`.
- `from Module/path import foo, bar` – import only the listed definitions.
- `from Module/path import foo as localFoo, bar as localBar` – selective import with per-name aliases.

Module paths use `/` and point to `.bend` files or directories. For example:

```bend
import Std/Nat as Nat
from Std/Vec import Vec, head as Vec/head
```

There is no wildcard import; every selective import must enumerate the desired names.

## Module Names and FQNs

`qualifyName` in `src/Core/Parse/Parse.hs` prefixes every `def`/`type` name with the module path of the file being parsed:

- `examples/prompt.bend` ⇒ module path `examples/prompt`.
- `Std/Vec/_.bend` ⇒ module path `Std/Vec`.

Definitions become keys like `examples/prompt::Nat/add`. The importer never strips this prefix; instead, it rewrites references to match it.

`Core.Import.extractModuleName` performs the inverse transformation when it needs to recover the module name from a file path. It removes the `.bend` suffix and the special `/_` suffix used by “directory modules”.

## Substitution Maps

Central to the system is `SubstMap`:

```haskell
data SubstMap = SubstMap
  { functionMap :: Map Name Name  -- short name → fully qualified name
  , enumMap     :: Map Name Name  -- enum constructor alias → FQN
  }
```

`substituteRefs` walks terms and types and replaces:

- `Ref`/`Var` names using `functionMap` (unless the variable is bound).
- `Sym` nodes (enum constructors) using `enumMap`, with special handling to avoid mangling already-qualified tags.

`buildLocalSubstMap` constructs a map for the current file so that unqualified mentions of locally defined functions are rewritten to their FQNs. It also inspects datatype definitions to register enum constructors under both their short name (`WLeaf`) and type-qualified form (`MyTree::WLeaf`), but only when the constructor is unambiguous across the entire book.

`unionSubstMap` is left-biased: the first map’s entries win. The importer uses this to make explicit aliases take precedence over automatic name generation.

## Explicit Import Resolution

`processExplicitImports` iterates over every parsed `Import` and resolves it through `resolveCascadingImport`:

1. **Local attempt (`resolveLocalImport`):**
   - Converts the module path into a list of possible file paths via `generateImportPaths`. Directories prefer a `/_` file (e.g. `Std/Nat/_.bend`); otherwise `Std/Nat.bend` is used.
   - The search is performed first in the workspace, then (if present) under `bend_packages/`.
   - When the file exists it is parsed with `doParseBook`, and a local substitution map is applied so the imported book is internally consistent.

2. **External fallback (`resolveExternalImport`):**
   - Only attempted when the path matches `owner/package/…`.
   - Uses `Package.Index.importDefinition` (backed by `src/Package/Index.hs`) to fetch the definition and all dependencies from a package index. The downloaded sources are cached under `bend_packages/owner/package#version/...`.
   - Once fetched, the importer falls back to the local path logic with the resolved (versioned) file.

### Module Imports

For `import Std/Nat` without alias the imported book is merged wholesale; the resulting substitution map is empty because all names remain fully qualified (`Std/Nat::add`, etc.).

With `import Std/Nat as NatOps` the importer builds an alias table covering:

- Every definition exported by the module, mapped as `NatOps::foo` → `Std/Nat::foo`.
- A “direct” alias (`NatOps` → `Std/Nat::path`) when the module has a definition that matches the original import path (`Std/Nat::Nat` when the module defines `def Std/Nat(...)`).

That alias table enters the global substitution map so that code can call either `NatOps::add` or (when the direct alias is available) just `NatOps`.

### Selective Imports

`from Std/Nat import add, mul as times` yields:

- A filtered book that only retains `Std/Nat::add` and `Std/Nat::mul` (other definitions are dropped from both the `Map` and the definition ordering list).
- Substitution entries `add` → `Std/Nat::add` and `times` → `Std/Nat::mul`.

Selective imports do not import enum constructors automatically; they rely on the imported definitions’ own references being already qualified.

`processExplicitImports` merges all imported books with `mergeBooks`, which preserves the original ordering (new names are appended). Substitution maps from individual imports are merged with `unionSubstMap`, so earlier imports win when aliases collide.

## Automatic Dependency Closure

After explicit imports (if any) are merged with the current file, the importer builds a starting worklist:

1. Apply the current substitution map to the book (`substituteRefsInBook`) so that local and explicitly imported aliases are inlined.
2. Run `getBookDeps` (`src/Core/Deps.hs`) to gather every free name referenced in the book’s terms and types. The dependency collector is HOAS-aware: it does not treat bound variables as dependencies and inspects pattern scrutinees, rewrite witnesses, etc.
3. Seed `importLoop` with that dependency set.

`ImportState` holds:

- `stVisited`: canonical file paths that were already parsed (prevents cycles and redundant parsing).
- `stLoaded`: names already satisfied (so repeated references do not re-trigger work).
- `stBook`: the accumulated book so far.
- `stSubstMap`: the global substitution map (aliases, local names, enum tags).
- `stCurrentFile`: only used when building the initial local substitution map.

### Resolving a Dependency

`importLoop` repeatedly:

1. Pick the lexicographically smallest pending reference.
2. Skip it if already loaded.
3. Otherwise, call `resolveRef`.

`resolveRef` handles several cases:

- **Alias-qualified reference (`Alias::foo`):** when the alias exists in `stSubstMap`, the entry already rewrites the name. The dependency is marked as loaded.
- **Single matching definition already in the book:** if exactly one FQN ends with `::refName`, auto-import is allowed *only when* the function name equals the module prefix. This rule enforces the “import the module by calling its module name” design:
  - `Nat/add` can auto-resolve to `Nat/add::Nat/add`.
  - `add` cannot auto-resolve to `examples/prompt::add`; you must use an explicit import.
- **Otherwise:** delegate to `loadRef`, which tries to interpret the reference as a module path and parse the corresponding file.

`loadRef`:

- Uses `generateImportPaths` and `firstExisting` to locate the file. The search order is workspace first, then `bend_packages`.
- Detects and reports missing `/_` files when a directory exists but lacks an entry point.
- After parsing the module, it applies the module’s own local substitutions and merges the resulting book into `stBook`.
- If the reference matches the module name (`Nat/add` referencing `Nat/add::Nat/add`), it inserts a substitution entry so that the ref rewrites to the FQN from now on.

After each successful resolution, the importer:

- Re-applies substitutions to the updated book.
- Recomputes dependencies (`getBookDeps`) so that newly imported definitions can contribute further references.
- Continues until no pending references remain.

Cycle detection is handled by `stVisited`: once a file path has been parsed it is never processed again. Re-importing the same module simply shares the existing definitions.

## Enum Constructor Handling

Enum constructors appear in code via the `Sym` term. When datatypes are parsed the constructors are recorded with fully qualified names (`Std/Tree::Leaf`, etc.). To let users write just `Leaf`, the importer:

- Scans datatype definitions (`Sig (Enu tags) …`) inside `buildLocalSubstMap` and registers short names, provided they are unambiguous across the entire book.
- When applying substitutions, `substituteInEnumName` rewrites constructor names while respecting already-qualified strings (`::` is inspected so that `Module::Type::Tag` stays untouched).
- Enum mappings are tracked separately from function mappings to avoid collisions between constructors and functions that happen to share the same name.

## External Packages and Caching

Any import whose path matches `owner/package/rest/of/path` is treated as a package index lookup:

1. `Package.Index.defaultIndexConfig` points to `http://localhost:3000` by default and uses `bend_packages/` as the cache directory.
2. `importDefinition` contacts the index, downloads the requested definition plus its dependency graph, and stores each `.bend` file locally under `bend_packages/<owner>/<package>#<version>/<path>.bend`.
3. The importer then restarts resolution using the now-localised path, so the rest of the pipeline is identical to regular local imports.

The cache directory participates in `generateImportPaths`, meaning that once a package has been downloaded it behaves like a regular module on subsequent runs.

## Error Reporting

The importer raises descriptive errors for the main failure modes:

- Missing module file: lists every attempted path when `firstExisting` fails.
- Directory modules without entry point: reports the missing `/_` file.
- Ambiguous references: when more than one FQN ends with the same suffix, the error lists all possibilities.
- Combined failures for cascading imports: if both local and external resolution fail, the final message shows both error strings.

Because substitutions are applied eagerly, most name resolution errors surface early, before type checking or evaluation.

## Worked Example

Given a file `app/Main.bend`:

```bend
import Std/Nat as Nat
from Std/List import map

def sum_to(n: Nat) -> Nat:
  match n:
    case 0n: 0n
    case 1n+k: Nat::add(n, sum_to(k))

def twice(n: Nat) -> Nat:
  Nat::add(n, n)
```

Resolution proceeds as follows:

1. The parser qualifies definitions as `app/Main::sum_to` and `app/Main::twice`, records both import directives, and initialises the local substitution map (`sum_to` → `app/Main::sum_to`, etc.).
2. The explicit imports load `Std/Nat` and `Std/List`, produce substitution entries such as `Nat::add` → `Std/Nat::add`, and merge those definitions into the book.
3. `getBookDeps` finds dependencies `Nat::add`, `Std/List::map`, plus the constructors used inside the imported modules.
4. `resolveRef` observes that `Nat::add` is already in the substitution map (from the alias), so nothing further is needed. Any other uncovered name triggers module loading until the dependency set becomes empty.

All references are now fully qualified; subsequent phases (`adjustBook`, type checking, evaluation, code generation) operate on that grounded book.

## Practical Notes and Limitations

- Auto-import is intentionally conservative: only references that equal their module name (`Foo/bar`) are auto-resolved. Use explicit imports for anything else.
- Aliases are pure rewrites. After substitution the original alias never appears again in the core language; tooling that inspects the book will only see FQNs.
- Selective imports drop unspecified definitions entirely; they are not merely hidden. If another module later requires a dropped definition it must import it explicitly.
- Enum constructor aliases are skipped when multiple constructors share the same short name. In that case you must use the fully qualified constructor (`Module::Type::Tag`).
- The package index URL is hard-coded today; adapt `Package.Index.defaultIndexConfig` if you run a different registry.

Together these rules provide a predictable path-based module system backed by deterministic rewriting. When writing tooling or new surface features, rely on the final book produced by the importer—every reference you see there is the canonical truth.

