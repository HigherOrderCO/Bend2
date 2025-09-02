# Bend Import System Specification

## Overview

This document specifies the import system for the Bend programming language. The system combines auto-import functionality with explicit qualified imports, providing both convenience and control over namespace management.

## Core Concepts

**Module**: A single `.bend` file containing function definitions.

**Namespace**: Each file creates its own namespace using the file path as a prefix.

**Book**: The final merged collection of all definitions after import resolution, where each definition has a fully qualified name.

**Fully Qualified Name (FQN)**: The complete path to a definition, formatted as `filepath::definition_name`.

## Naming Convention

All definitions in the compiled Book use fully qualified names:

```
FQN = filepath::definition_name

Examples:
- From Nat/add.bend: `Nat/add` becomes `Nat/add::Nat/add`
- From b.bend: `Nat/add` becomes `b::Nat/add`
- From utils/math.bend: `sqrt` becomes `utils/math::sqrt`
```

## Import Resolution Algorithm

The import system follows a three-phase resolution process with strict precedence rules:

```
PRECEDENCE: LOCAL > IMPORTED > AUTO-IMPORTED
```

### Phase 1: Parse and Collect Local Definitions
- Parse the current file
- Collect all function definitions in the file
- These become the local namespace with highest precedence

### Phase 2: Process Explicit Imports
- Process import statements in order (top to bottom)
- Later imports overwrite earlier imports with the same name
- Build the imported namespace

### Phase 3: Resolve Names
For each name reference in the code:
1. Check if it exists in local definitions → use local FQN
2. Check if it exists in imported definitions → use imported FQN
3. Attempt auto-import → search for matching file path
4. If none found → compilation error

### Auto-Import Resolution
Auto-import ONLY searches for files matching the exact name pattern:
```
For name "Foo/Bar/Baz":
1. Try: Foo/Bar/Baz.bend
2. Try: Foo/Bar/Baz/_.bend
3. If found and contains definition "Foo/Bar/Baz" → import it
4. Otherwise → fail
```

## Import Syntax

### Import Entire Module
```python
import b                        # All definitions from b.bend available as b::name
import utils/math              # All definitions available as utils/math::name
```

### Import Specific Definitions
```python
from b import Nat/add          # Nat/add now refers to b::Nat/add
from utils/math import sqrt, pow  # Multiple imports
```

### Import with Aliases
```python
import very/long/path as vlp  # Access as vlp::definition
from b import Nat/add as add  # add now refers to b::Nat/add
```

## Compilation Process

### Step 1: Parse All Files
```
- Parse all .bend files in the project
- Extract function signatures and definitions
- Build initial AST for each file
- Collect all local definitions per file
```

### Step 2: Build Dependency Graph
```
- Identify all import statements
- Map import paths to actual files
- Detect circular dependencies (error if found)
- Determine compilation order
```

### Step 3: Resolve Imports
```
For each file in dependency order:
  1. Start with empty namespace
  2. Process explicit imports sequentially
  3. Build import table with FQNs
  4. Track shadowing for warnings
```

### Step 4: Name Resolution
```
For each file:
  For each name reference:
    1. If defined locally → replace with local_file::name
    2. If explicitly imported → replace with imported FQN
    3. If neither → attempt auto-import
    4. Replace reference with resolved FQN
```

### Step 5: Generate Book
```
- Merge all definitions with their FQNs
- Ensure no duplicate FQNs exist
- Apply any post-processing optimizations
- Output final Book structure
```

## Book Structure

The final Book is a flat map of FQN to definition:

```javascript
Book = {
  "Nat/add::Nat/add": {
    type: "function",
    body: <parsed_ast>,
    // ... other metadata
  },
  "b::Nat/add": {
    type: "function", 
    body: <parsed_ast>,
    // ... other metadata
  },
  "b::b": {
    type: "function",
    body: <parsed_ast_calling_b::Nat/add>,
    // ... other metadata
  },
  "a::main": {
    type: "function",
    body: <parsed_ast_calling_Nat/add::Nat/add>,
    // ... other metadata
  }
}
```

## Key Design Rules

### Rule 1: No Transitive Imports
Imports do not leak across module boundaries. If module A imports B, and B imports C, module A does NOT get access to C's definitions unless it explicitly imports C.

### Rule 2: File-Path Determinism
Auto-import ALWAYS maps to file structure. The name `Foo/Bar` will ONLY attempt to load from:
- `Foo/Bar.bend`
- `Foo/Bar/_.bend`

It will NEVER search inside other files for a matching definition.

### Rule 3: Exact Name Matching
For auto-import to work, the function name must EXACTLY match what would be searched:
```python
# In List/map.bend:
def map(): ...          # ❌ Won't be auto-imported as List/map
def List/map(): ...     # ✅ Will be auto-imported as List/map
```

### Rule 4: Last Import Wins
When multiple explicit imports define the same name, the last one takes precedence:
```python
from module1 import foo  # foo = module1::foo
from module2 import foo  # foo = module2::foo (overwrites)
```

### Rule 5: Local Definitions Have Highest Precedence
Local definitions always override imported names:
```python
import Nat              # Imports Nat::Nat/add
def Nat/add(): ...     # Local definition wins
```

### Rule 6: Imports Must Be at File Top
All import statements must appear before any function definitions in the file.

## Error Handling

### Circular Dependencies
```
Error: Circular dependency detected:
  a.bend → b.bend → c.bend → a.bend
```

### Missing Auto-Import Target
```
Error: Cannot auto-import 'Foo/Bar'
  No file found at: Foo/Bar.bend or Foo/Bar/_.bend
```

### Name Conflict Warnings
```
Warning: In b.bend:
  Local definition 'Nat/add' shadows auto-imported 'Nat/add::Nat/add'
  Consider using explicit import or renaming local definition
```

### Import Not Found
```
Error: Cannot import module 'nonexistent/module'
  File not found: nonexistent/module.bend
```

## Debug Output

### Full FQN Display
When displaying errors or debug information, show the full FQN when necessary for clarity:
```
Error: Type mismatch in b::Nat/add
  Expected: Nat -> Nat -> Nat
  Found: Nat -> Nat -> String
  
Stack trace:
  at a::main (a.bend:15)
  at b::compute (b.bend:8)
```

### Configurable Name Display
Provide flags for controlling how names are displayed:
- `--show-full-names`: Always show complete FQNs
- `--show-short-names`: Show minimal distinguishing names (default)

## Implementation Notes

### Caching Strategy
- Cache parsed ASTs keyed by file content hash
- Cache import resolution results per compilation
- Invalidate only affected modules when files change

### Parallel Processing
- Files can be parsed in parallel
- Import resolution must respect dependency order
- Name resolution can be parallelized per file after imports are resolved

### Symbol Table Structure
Each file maintains a symbol table during compilation:
```python
FileSymbolTable = {
  local_definitions: Map<string, Definition>,
  imported_symbols: Map<string, FQN>,
  auto_imports_used: Set<string>
}
```

### Resolution Function Pseudocode
```python
def resolve_name(name: str, file_context: FileContext) -> FQN:
    # Check local definitions
    if name in file_context.local_definitions:
        return f"{file_context.filepath}::{name}"
    
    # Check explicit imports
    if name in file_context.imported_symbols:
        return file_context.imported_symbols[name]
    
    # Try auto-import
    for candidate in [f"{name}.bend", f"{name}/_.bend"]:
        if exists(candidate):
            module = load_module(candidate)
            if name in module.exports:
                return f"{candidate_without_extension}::{name}"
    
    raise NameError(f"Undefined name: {name}")
```

## Invariants

The following invariants MUST be maintained by the implementation:

1. **No circular dependencies**: The dependency graph must be acyclic
2. **Unique FQNs**: Each FQN in the final Book must be unique
3. **Deterministic resolution**: Given the same inputs, name resolution must always produce the same output
4. **Isolation**: Changes to imported modules cannot affect the importing module's local definitions
5. **Order preservation**: Import order must be preserved as it affects precedence
6. **File-definition correspondence**: Auto-imported names must correspond to actual file paths

## Example Walkthrough

Given the following files:

**Nat/add.bend**
```python
def Nat/add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      return b
    case 1n+p:
      return 1n + Nat/add(p, b)
```

**b.bend**
```python
def Nat/add(a: Nat, b: Nat) -> Nat:
  return 1n

def b() -> Nat:
  return Nat/add(1n, 1n)  # Uses local b::Nat/add
```

**a.bend**
```python
from b import b

def main() -> Nat:
  x = b()                 # Calls b::b which returns 1n
  return Nat/add(x, 0n)   # Auto-imports Nat/add::Nat/add
```

**Resulting Book:**
```javascript
{
  "Nat/add::Nat/add": <recursive_add_implementation>,
  "b::Nat/add": <returns_1n>,
  "b::b": <calls_b::Nat/add>,
  "a::main": <calls_b::b_then_Nat/add::Nat/add>
}
```

This specification provides a complete, unambiguous definition of the Bend import system that can be implemented consistently.
