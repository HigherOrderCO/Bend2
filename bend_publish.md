
# Bend-publish command

This is the specification for the Bend publish command feature.

This command is related to `docs/import-system.md`, so read it.

Basically, this command will be used for a user that wants to publish a specific library to our `BendRoot`, the centralized index of packages.

Remember that this assumes that the user will always be working on a `BendRoot/` path (and bend should guarantee that).

The flow should be the following:
- User is writing programs on `BendRoot/@username` where `@username` is that user github username.
- User writes a lib: `BendRoot/@lorenzo/Math/add.bend`
- Now, user wants to publish this lib, and runs `bend publish`

We have some challenges here. The user must be authenticated through github, and also the user should be able to *choose* what is going to be published.

So this `bend publish` command should be more a `cli-like` tool, that allows choosing some stuff.
Therefore, first of all, when running `bend publish`, it should check / try to authenticate the user.
I think this should be possible through some link, like "click that link, authenticate in the browser and come back". Then, if this worked, we should open something similar to `lazygit` that will basically lists the repositories / libs under `BendRoot/@username` so the user can choose which one it will publish.

Once chosen, we should call the Bend package index API that will correctly publish the package and return the success / failure feedback and the updated version (and something like "oh you can use it via `@lorenzo/Math/add` now.

The api documentation is at @API_doc.md

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
