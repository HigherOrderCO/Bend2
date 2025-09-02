
# Bend Package Manager Specification

## Overview

This document specifies the package manager for the Bend programming language. The system is designed to integrate seamlessly with the existing import system while providing direct GitHub repository access without traditional package manager complexity like lock files or complex configurations.

## Core Design Principles

1. **Minimal Configuration**: No lock files, package.json equivalents, or complex configuration files
2. **Direct GitHub Access**: Import packages directly from GitHub repositories  
3. **Global Package Cache**: All packages stored in a global cache directory for sharing across projects
4. **Import System Integration**: Extends existing import syntax and resolution mechanisms
5. **Content-Addressable Storage**: Packages identified by content hash for reliable versioning
6. **Non-Intrusive**: Does not modify existing project files or create package metadata in projects

## Package Import Syntax

### GitHub Repository Imports

```python
# Import entire repository using repository name as package name
import "gh:owner/repo"

# Import repository with custom alias
import "gh:owner/repo" as customName

# Import specific branch or tag 
import "gh:owner/repo@branch-name"
import "gh:owner/repo@v1.2.3"

# Import specific commit hash
import "gh:owner/repo@commit-hash"

# Import subdirectory from repository
import "gh:owner/repo/subpath"
import "gh:owner/repo/subpath@branch"

# Selective imports from GitHub packages
from "gh:owner/repo" import Module/function
from "gh:owner/repo@v1.0.0" import Util/helper as helper
```

### Integration with Existing Import System

GitHub imports extend the existing import syntax and integrate with current resolution:

```python
# Local imports (unchanged)
import Nat/add
from List import map, filter

# GitHub imports 
import "gh:bend-lang/std"

# Mixed usage
def main():
  x = Nat/add(1n, 2n)        # Local import
  y = std/Math/sqrt(16n)     # From GitHub package gh:bend-lang/std
  return x + y
```

## Package Storage Architecture

### Directory Structure

```
~/.bend/packages/
├── cache/
│   ├── github.com/
│   │   └── owner/
│   │       └── repo/
│   │           ├── commit-hash-1/
│   │           │   ├── .bend-pkg-meta
│   │           │   └── [repo contents]
│   │           └── commit-hash-2/
│   │               ├── .bend-pkg-meta
│   │               └── [repo contents]
│   └── index/
│       ├── github.com-owner-repo-main -> ../github.com/owner/repo/commit-hash-1
│       ├── github.com-owner-repo-v1.0.0 -> ../github.com/owner/repo/commit-hash-2
│       └── url-hash-mappings.json
├── temp/
│   └── [temporary download directories]
└── config/
    └── cache-config.json
```

### Package Metadata Format

Each package directory contains a `.bend-pkg-meta` file:

```json
{
  "source": {
    "type": "github",
    "owner": "bend-lang",
    "repo": "std",
    "ref": "main",
    "commit": "a1b2c3d4...",
    "url": "https://github.com/bend-lang/std.git"
  },
  "downloaded": "2024-01-15T10:30:00Z",
  "content_hash": "sha256:...",
  "bend_files": [
    "Nat/add.bend",
    "List/map.bend",
    "String/utils.bend"
  ],
  "dependencies": [
    "gh:other-org/math-lib@v2.1.0"
  ]
}
```

## Versioning and Content Addressing

### Content Hashing Strategy

1. **Repository Content Hash**: SHA256 of all `.bend` files and directory structure
2. **Immutable References**: Once downloaded, package content never changes
3. **Multiple Versions**: Different commits/tags stored separately
4. **Garbage Collection**: Unused packages removed based on access time

### Version Resolution Rules

```
PRIORITY: EXPLICIT_VERSION > LATEST_TAG > MAIN_BRANCH
```

1. **Explicit Version**: `gh:owner/repo@v1.2.3` → exact tag/commit
2. **Branch Reference**: `gh:owner/repo@main` → latest commit on branch  
3. **No Version**: `gh:owner/repo` → latest semver tag, fallback to main branch

## Import Resolution Integration

We need to integrate with the current import system. The current import system works with fully qualified names based on the current package (root repository).

This means that if root = "./", and we have "./Nat/add.bend" , and in this file we have "def Nat/add()", it's path is: "Nat/add::Nat/add". This works for all functions and types.

However, since we're working with packages now, we need their path. Basically we need to integrate them into our project. We probably shouldnt use their entire path because it will be too long and refer to outside of the project (i.e cache). So, we use the fully qualified name relative to place where that code lives. However this may not work because then we can't use the same resolving technique.

So, what we're going to do is the following:

When installing a package, we maintain a global index (as we already do) of versions and installments of packages.

However, when importing it in a project, we copy the project to something similar to a `node_modules` inside of the project. This way the resolving is much easier then if we have an outside path, because now we have `./` as the root and we can make like `./bend_packages` or `/.bend_packages/` as the project's modules, and then the wanshi lib can live at: `./bend_packages/WanShi`, for example. 

This makes the approach suitable for the current import resolution, in a way that we basically don't have to do nothing for it to work.

## Package Download and Caching

### HTTP Client Implementation

```haskell
-- src/Core/Package/HTTP.hs
module Core.Package.HTTP where

data GitHubAPI = GitHubAPI
  { apiGetRepo :: Owner -> Repo -> IO (Either String RepoInfo)
  , apiGetRef  :: Owner -> Repo -> Ref -> IO (Either String CommitInfo)  
  , apiDownloadArchive :: Owner -> Repo -> CommitHash -> IO (Either String FilePath)
  }

-- Use existing Haskell HTTP libraries
downloadRepository :: GitHubImport -> IO (Either String FilePath)
```

### Caching Strategy

```haskell
-- src/Core/Package/Cache.hs  
module Core.Package.Cache where

data CacheManager = CacheManager
  { cacheDir :: FilePath
  , maxCacheSize :: Integer  -- bytes
  , maxAge :: Integer        -- seconds
  }

cachePackage :: GitHubImport -> CommitHash -> [FilePath] -> IO (Either String FilePath)
getCachedPackage :: String -> IO (Maybe FilePath)
cleanupCache :: CacheManager -> IO ()
```

### Download Process

1. **Parse Import**: Extract owner, repo, ref from `gh:owner/repo@ref`
2. **Resolve Reference**: Use GitHub API to resolve branch/tag to commit hash
3. **Check Cache**: Look for existing cached version by commit hash
4. **Download**: If not cached, download repository archive
5. **Extract**: Extract archive to cache directory with commit hash
6. **Index**: Create symbolic link in index for quick lookup
7. **Validate**: Verify all `.bend` files parse correctly
8. **Register**: Add to package cache mappings

## Error Handling

### GitHub Import Errors

```
Error: Cannot resolve GitHub import 'gh:owner/nonexistent'
  Repository not found: https://github.com/owner/nonexistent
  
Error: Invalid reference in 'gh:owner/repo@invalid-branch'  
  Reference 'invalid-branch' does not exist in repository
  Available branches: main, develop, feature/new
  Available tags: v1.0.0, v1.1.0, v2.0.0

Error: Network failure while downloading 'gh:owner/repo'
  Failed to connect to github.com
  Check your internet connection and try again
  
Warning: Package 'gh:owner/repo' contains no .bend files
  Imported package has no Bend modules to use
```

### Version Conflicts

```
Error: Version conflict for package 'math-utils'
  main.bend imports gh:org1/math-utils@v1.0.0
  helper.bend imports gh:org1/math-utils@v2.0.0
  
  Resolution strategies:
  1. Use explicit version in all imports
  2. Update all imports to compatible version
  3. Use package aliasing: import gh:org1/math-utils@v1.0.0 as mathV1
```

### Circular Dependencies

```
Error: Circular dependency detected in GitHub packages:
  gh:org1/package-a → gh:org2/package-b → gh:org1/package-a
  
  Package dependency chain:
  - package-a depends on package-b
  - package-b depends on package-a
```

## Command Line Interface

### New CLI Commands

```bash
# Install/update packages (download and cache)
bend package install gh:owner/repo
bend package install gh:owner/repo@v1.0.0

# List installed packages
bend package list
bend package list --verbose

# Show package information
bend package info gh:owner/repo
bend package info owner/repo  # shorthand

# Clean package cache  
bend package clean
bend package clean --all

# Update packages
bend package update
bend package update gh:owner/repo

# Remove unused packages
bend package gc
```

### Integration with Existing Commands

```bash
# Existing commands work transparently with GitHub imports
bend main.bend                    # Auto-downloads GitHub dependencies
bend main.bend --no-package       # Skip GitHub package resolution
bend deps main.bend               # Show all deps including GitHub packages
bend check main.bend              # Type-check with GitHub packages
```

## Security Considerations

### Package Verification
- Verify downloaded packages contain only `.bend` files and safe content
- Hash validation to ensure package integrity
- Rate limiting for GitHub API requests

### Network Security  
- HTTPS-only connections for all GitHub API calls
- Timeout handling for network requests
- Graceful degradation when offline

### Cache Security
- Proper file permissions on cache directory
- Protection against directory traversal attacks
- Safe extraction of downloaded archives

## Backwards Compatibility

### Existing Import System
- All existing import syntax continues to work unchanged
- Local imports take precedence over GitHub imports
- No changes to existing project files required

### Migration Path
- GitHub imports are purely additive
- Existing projects work without modification
- Optional adoption of GitHub packages

This specification provides a complete, implementable design for the Bend package manager that integrates seamlessly with the existing import system while providing powerful GitHub-based package management capabilities.
