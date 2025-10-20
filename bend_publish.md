
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

## Friendlier Authentication Flow (Future Work)

To avoid asking the user to manually extract the `connect.sid` cookie from their browser, Bend should adopt a device/PKCE style login flow. The CLI and the server share responsibility for this workflow.

### CLI Requirements

- When `bend publish` needs authentication it must call a new endpoint (see server list below) that returns a payload containing:
  - `deviceCode` – opaque identifier used for polling.
  - `userCode` – short alphanumeric code the user types in the browser (for devices that cannot open a URL automatically).
  - `verificationUrl` – the URL the user visits to approve access.
  - `pollInterval` – minimum seconds between poll attempts.
- The CLI must:
  1. Display the `verificationUrl` and `userCode`, and attempt to open the default browser with the verification URL (using `open`/`xdg-open`/`start`).
  2. Poll the server at the provided interval until the user authorizes or the code expires.
  3. On success, receive a Bend session token (`connect.sid` or another CLI-scoped session) and persist it in `~/.bend/session.json` (same storage as today).
  4. Handle timeout/denied states gracefully, showing the error and allowing the user to retry or fall back to the manual cookie method (e.g., `bend publish --manual-cookie`).
- Polling must back off on `slow_down` responses and abort after the server reports `expired` or a max wall-clock timeout.

### Server Requirements

- Expose new endpoints to support the device flow:
  - `POST /auth/device/start` → returns `{ deviceCode, userCode, verificationUrl, pollInterval, expiresIn }`.
  - `GET /auth/device/poll?code=<deviceCode>` → returns the session when approved, or status codes (`pending`, `slow_down`, `denied`, `expired`).
- On `start`, store the pending device request (code, expiry, associated GitHub OAuth state). Enforce TTL cleanup to prevent stale codes.
- Update the existing GitHub OAuth callback so that when the user authorizes in the browser (using `verificationUrl` + `userCode`), the server:
  - Matches the pending `deviceCode`.
  - Completes the OAuth exchange.
  - Issues a Bend session cookie, recording it against the pending device request.
- Ensure `poll` only returns the session to the CLI over HTTPS. For `pending`, just echo the status. For `slow_down`, include a suggestion for the new interval. For `denied`/`expired`, return an error message so the CLI can surface it.
- Document the new endpoints in `API_doc.md` and keep the legacy manual-cookie instructions as a fallback until all clients adopt the new flow.
