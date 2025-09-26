# Enum Resolution Algorithm

The Enum Resolution module extends Bend's Fully Qualified Name (FQN) system to enum values, ensuring global uniqueness of enum references across the entire codebase. This transformation resolves ambiguous enum names by prefixing them with their type's FQN.

## Overview

The main goal is to eliminate ambiguous enum references by converting them into globally unique identifiers. This builds upon Bend's import system, extending the FQN concept from definitions to enum values within those definitions.

```haskell
-- Before resolution
Sym "Circle"              -- Which Circle? Could be from any type

-- After resolution
Sym "shapes::Shape::Circle"  -- Unambiguous reference
```

This transformation is essential for:
1. **Global Uniqueness**: Preventing name conflicts across modules and types
2. **Import System Integration**: Extending FQN semantics to enum values
3. **Error Prevention**: Catching ambiguous enum references at compile time

## Algorithm Components

### 1. Entry Point (`resolveEnumsInBook`)

```haskell
resolveEnumsInBook :: Book -> Result Book
resolveEnumsInBook book@(Book defs names) = do
  let emap = extractEnums book
  resolvedDefs <- M.traverseWithKey (\_ defn -> resolveEnumsInDefn emap defn) defs
  Done (Book resolvedDefs names)
```

The entry point follows a two-phase approach:
1. **Extraction Phase**: Build enum mapping from all type definitions
2. **Resolution Phase**: Apply the mapping to resolve all enum references

### 2. Enum Extraction (`extractEnums`)

This phase scans the entire Book to build an `EnumMap` that maps enum names to their possible FQNs.

```haskell
type EnumMap = M.Map String [String]  -- name -> [possible FQNs]
```

#### Extraction Strategy (`extractFromDefn`)

The extraction process looks for enum definitions in various contexts within type definitions:

```haskell
-- Direct enum type definition
Enu ["Red", "Green", "Blue"] -> foldr (addEnum "Color") emap ["Red", "Green", "Blue"]

-- Enum as first component of Sigma type (common pattern)
Sig (Enu ["Success", "Error"]) _ -> foldr (addEnum "Result") emap ["Success", "Error"]

-- Location-wrapped definitions
Loc _ innerTerm -> extractFromDefn typeName (True, innerTerm, Set) emap

-- Generic types with All (forall)
All _ body -> extractFromDefn typeName (True, body, Set) emap

-- Parameterized types with Lam
Lam _ _ body -> extractFromDefn typeName (True, body (Var "dummy" 0), Set) emap
```

#### Mapping Generation (`addEnum`)

For each discovered enum, multiple mappings are created to support flexible resolution:

```haskell
-- Given: typeFQN = "shapes::Shape", enumName = "Circle"
-- Creates mappings:
baseName = "Circle"           -- Extract base name from potential FQN
typeName = "Shape"            -- Extract type name from typeFQN
qualifiedName = "Shape::Circle" -- Create type::enum pattern

-- Add to EnumMap:
"Circle" -> ["shapes::Shape::Circle"]        -- Base name lookup
"Shape::Circle" -> ["shapes::Shape::Circle"] -- Qualified lookup
"shapes::Shape::Circle" -> ["shapes::Shape::Circle"] -- FQN lookup
```

This multi-level mapping enables resolution of:
- Simple names: `@Circle` → `shapes::Shape::Circle`
- Qualified names: `@Shape::Circle` → `shapes::Shape::Circle`
- Full FQNs: `@shapes::Shape::Circle` → `shapes::Shape::Circle`

### 3. Enum Resolution (`resolveEnum`)

This function resolves a single enum name using the built EnumMap:

```haskell
resolveEnum :: Span -> EnumMap -> String -> Result String
resolveEnum span emap enumName =
  case M.lookup enumName emap of
    Nothing -> Done enumName     -- Not found, leave as-is
    Just [fqn] -> Done fqn      -- Unique match, use it
    Just fqns ->                -- Ambiguous, error with suggestions
      Fail $ AmbiguousEnum span (Ctx []) enumName fqns
        (Just $ "Please use one of: " ++ intercalate ", " (map ("&" ++) fqns))
```

#### Resolution Logic:
1. **Not found**: Enum name isn't in the map → leave unchanged (might be external)
2. **Unique match**: Exactly one FQN maps to this name → use it
3. **Ambiguous**: Multiple FQNs map to this name → compilation error with suggestions

### 4. Term Traversal (`resolveEnumsInTerm`)

This phase recursively walks through all terms to find and resolve enum references:

#### Primary Enum Usage (`Sym`)

```haskell
-- Direct enum symbols
Sym name -> do
  resolved <- resolveEnum noSpan emap name
  Done (Sym resolved)

-- Location-wrapped symbols (preserves error reporting context)
Loc span (Sym name) -> do
  resolved <- resolveEnum span emap name  -- Use actual span
  Done (Loc span (Sym resolved))
```

#### Pattern Matching (`EnuM`)

```haskell
-- Enum pattern matching: λ{@Red: r; @Blue: b; def}
EnuM cases def -> do
  resolvedCases <- mapM resolveCase cases  -- Resolve each case
  resolvedDef <- go def                    -- Resolve default branch
  Done (EnuM resolvedCases resolvedDef)

-- Individual case resolution
resolveCase (enumName, body) = do
  resolvedEnum <- resolveEnum noSpan emap enumName
  resolvedBody <- go body
  Done (resolvedEnum, resolvedBody)
```

#### Special Syntax Handling (`Tup`)

The algorithm handles enum constructor syntax `@Enum{fields}` which desugars to tuples:

```haskell
-- @Success{value} desugars to (Sym "Success", value)
Tup (Sym name) rest -> do
  resolved <- resolveEnum noSpan emap name
  resolvedRest <- go rest
  Done (Tup (Sym resolved) resolvedRest)

-- With location information
Tup (Loc span (Sym name)) rest -> do
  resolved <- resolveEnum span emap name  -- Preserve span for errors
  resolvedRest <- go rest
  Done (Tup (Loc span (Sym resolved)) resolvedRest)
```

#### HOAS Handling

The algorithm properly handles Higher-Order Abstract Syntax (HOAS) constructs:

```haskell
-- Lambda functions
Lam k t f -> do
  t2 <- mapM go t                          -- Resolve type annotation
  Done $ Lam k t2 (\u -> case go (f u) of  -- Resolve body with error handling
    Done t -> t
    Fail e -> throw (BendException e))

-- Let bindings, Fix points, Use statements follow similar pattern
```

### 5. Book-Level Processing

The final phase applies enum resolution to all definitions:

```haskell
resolveEnumsInDefn :: EnumMap -> Defn -> Result Defn
resolveEnumsInDefn emap (inj, term, typ) = do
  resolvedTerm <- resolveEnumsInTerm emap term  -- Resolve definition body
  resolvedType <- resolveEnumsInTerm emap typ   -- Resolve type signature
  Done (inj, resolvedTerm, resolvedType)
```

## Integration with Import System

Enum resolution builds directly on Bend's import system architecture:

### FQN Extension Pattern

```haskell
-- Import system FQNs
"filepath::definition_name"

-- Enum resolution extends this to:
"filepath::TypeName::EnumValue"
```

### Resolution Precedence

Just as the import system has precedence rules (LOCAL > IMPORTED > AUTO-IMPORTED), enum resolution follows similar principles:

1. **Exact FQN**: `@module::Type::Enum` always resolves to itself
2. **Qualified name**: `@Type::Enum` resolves if unambiguous across types
3. **Base name**: `@Enum` resolves if unambiguous across the entire project

### Module Boundary Respect

Enum resolution respects module boundaries established by the import system:
- Enums are scoped to their defining module
- Cross-module enum references use full FQNs
- Local enum definitions shadow imported ones (following import precedence)

## Transformation Examples

### Example 1: Simple Resolution

**Input Types:**
```bend
// shapes.bend
type Shape = {&Circle, &Square, &Triangle}

// colors.bend
type Color = {&Red, &Green, &Blue}
```

**Input Code:**
```bend
// main.bend
def getRedCircle() -> (Shape, Color):
  (@Circle, @Red)  // Ambiguous without resolution
```

**EnumMap Construction:**
```haskell
EnumMap {
  "Circle"  -> ["shapes::Shape::Circle"],
  "Square"  -> ["shapes::Shape::Square"],
  "Triangle"-> ["shapes::Shape::Triangle"],
  "Red"     -> ["colors::Color::Red"],
  "Green"   -> ["colors::Color::Green"],
  "Blue"    -> ["colors::Color::Blue"]
}
```

**Output Code:**
```bend
def getRedCircle() -> (Shape, Color):
  (@shapes::Shape::Circle, @colors::Color::Red)
```

### Example 2: Ambiguous Resolution Error

**Input Types:**
```bend
// shapes.bend
type Shape = {&Circle, &Square}

// objects.bend
type Object = {&Circle, &Rectangle}  // Circle conflicts!
```

**Input Code:**
```bend
def makeCircle():
  @Circle  // Ambiguous - which Circle?
```

**Resolution Result:**
```
Error: AmbiguousEnum at main.bend:2:3
  Ambiguous enum name: Circle
  Multiple definitions found: shapes::Shape::Circle, objects::Object::Circle
  Please use one of: @shapes::Shape::Circle, @objects::Object::Circle
```

### Example 3: Pattern Matching Resolution

**Input:**
```bend
type Result<T,E> = {&Success{T}, &Error{E}}

def handleResult<T,E>(r: Result<T,E>) -> String:
  match r:
    case @Success{value}: "Got: " + show(value)
    case @Error{err}: "Error: " + show(err)
```

**After Resolution:**
```bend
def handleResult<T,E>(r: Result<T,E>) -> String:
  match r:
    case @Result::Success{value}: "Got: " + show(value)
    case @Result::Error{err}: "Error: " + show(err)
```

## Error Handling and Diagnostics

### Ambiguous Enum Errors

When multiple enums share the same name, the algorithm provides helpful diagnostics:

```haskell
AmbiguousEnum span (Ctx []) enumName fqns
  (Just $ "Please use one of: " ++ intercalate ", " (map ("&" ++) fqns))
```

**Error Message Example:**
```
Error: Ambiguous enum 'Status' at main.bend:15:8
  Found in multiple types:
    - http::Response::Status
    - task::Job::Status
    - user::Account::Status
  Please use one of: @http::Response::Status, @task::Job::Status, @user::Account::Status
```

### Location Preservation

The algorithm preserves source location information through transformations:

```haskell
-- Original location information is maintained
Loc span (Sym name) -> do
  resolved <- resolveEnum span emap name  -- Use original span for errors
  Done (Loc span (Sym resolved))
```

This ensures error messages point to the correct source locations even after transformation.

### Exception Handling for HOAS

Since HOAS constructs use Haskell functions, compile-time errors must be handled specially:

```haskell
Lam k t2 (\u -> case go (f u) of
  Done t -> t;
  Fail e -> throw (BendException e))  -- Convert to runtime exception
```

## Key Properties

1. **Global Uniqueness**: No two enum values can have the same FQN
2. **Import System Consistency**: Follows same FQN patterns as definitions
3. **Module Encapsulation**: Respects module boundaries from import resolution
4. **Location Preservation**: Maintains source spans for accurate error reporting
5. **Backwards Compatibility**: Unresolved names are left unchanged (for external enums)
6. **Deterministic Resolution**: Same inputs always produce same outputs
7. **HOAS Preservation**: Maintains higher-order abstract syntax throughout

## Compilation Pipeline Integration

Enum resolution fits into the broader compilation pipeline:

```haskell
1. Parse Phase:        .bend files → AST with Sym nodes
2. Import Resolution:  AST → AST with FQNs for definitions
3. Enum Resolution:    AST → AST with FQNs for enums     [THIS PASS]
4. Pattern Flattening: AST → AST with simple patterns
5. Type Checking:      AST → Typed AST
6. Code Generation:    Typed AST → Target code
```

### Prerequisites
- **Import resolution must complete first**: Enum FQNs depend on type definition FQNs
- **Type definitions must be available**: Cannot resolve enums without knowing their types

### Postconditions
- **All enum references are either resolved or marked as external**
- **No ambiguous enum names remain in the code**
- **Error reporting includes full context for debugging**

