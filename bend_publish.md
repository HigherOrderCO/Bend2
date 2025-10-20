
# Bend publish & bump commands

Every package that lives under `BendRoot/@<username>` is published as a
versioned *module snapshot*. Snapshot directories must follow the pattern
`module=<version>` (for example `@lorenzo/Math=4`).  A snapshot is immutable:
once `Math=4` is published it can never be modified, and a new version must be
created instead.

Key rules:

- All directories directly under `@<username>` must already carry a version
  suffix (`=0`, `=1`, …). A directory without a version is treated as an error
  and the CLI aborts with a helpful message.
- All imports and internal references must use the same `=<version>` syntax.
  The CLI does not attempt to infer the version of a reference.

### Publishing

- `bend publish` authenticates (device flow or manual cookie) and attempts to
  publish every versioned module under `@<username>`.
- `bend publish <module>` publishes a single module. The argument can be either
  `module=N` (explicit snapshot) or just `module` (the CLI picks the highest
  local version).
- Before uploading, the CLI queries the package index:
  - If the version already exists remotely, the publish is rejected with an
    error like `module Math=3 already published; run 'bend bump Math'`.
  - Otherwise the CLI streams the snapshot using canonical paths
    `@<username>/module=N/...`.
- When multiple modules are present, the CLI simply walks them all

### Bumping

- `bend bump <module>` creates the next version of a module.
  - The command renames the latest local snapshot to
    `=<next-version>`.
  - It updates every occurrence of `@<username>/module=old` inside the new
    snapshot to reference the new version.
  - The new version is chosen so that it is strictly greater than both the local
    snapshot and the latest published version reported by the API.
  - After the bump you can edit the new directory and run `bend publish`.

### Directory Workflow Summary

1. Start a module at `BendRoot/@user/module=1`.
2. Write code referencing other modules with explicit `=version` segments.
3. When ready, run `bend publish [module]`. The CLI uploads each snapshot that
   has not been published before.
4. To iterate on a published module, execute `bend bump module` and then edit
   the freshly created `module=next` directory.
