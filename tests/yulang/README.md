# Yulang Regression Fixtures

Small `.yu` files in this tree are shared regression inputs.
Rust tests can load them today, and a future Yulang test runner can reuse the
same files without copying source text out of inline strings.

`cases.toml` is the public contract manifest. It names the small fixtures that
currently define the executable language floor for CLI runtime, diagnostics,
runtime error, compile error, and public signature behavior. Each entry should
point at a focused `.yu` file and list the contract tags it protects.
`yulang contract tests/yulang/cases.toml` runs the same manifest through the
release binary surface; pass `--std-root lib` when running it from a repository
checkout. Use `--contract stable-core` to run the Contract v0 subset, or repeat
`--contract <tag>` to require multiple tags. Repeat `--case <name>` to run a
focused set in one runner invocation; release smoke uses this for the
representative file-resource evidence.
The manifest runner checks that `run` cases carry a runtime-facing tag, `check`
cases carry `diagnostics`, and `public-signature` cases carry
`public-signature`, so the tags remain useful as a contract index rather than
free-form notes.
Contract tags use lowercase ASCII letters, digits, `.`, and `-` only.
They are also checked against the manifest runner's known tag set, so new tags
must be deliberately added to the taxonomy instead of appearing as ad-hoc notes.
`runtime-error` cases must set `expect_success = false` and be classified as
exactly one of `runtime-failure` or `compile-error`; `compile-error` cases also
carry `diagnostics`, because their current contract is the user-facing compile
error text rather than a completed runtime path. A `compile-error` tag is a
run-only migration marker: add a separate `kind = "check"` case when the same
failure has structured `SourceDiagnostic` coverage. These cases should assert a
matching `compile error [` or `runtime error [` stderr prefix.
`public-example` cases must point at `examples/` from the repo root; and
`standard-api` cases must name a narrower API area such as `result`, `errors`,
`path`, `str`, `time`, or `file`. Standard file API cases must also declare a host scope
such as `host.native` or `host.unsupported`; the broad `host` tag is
intentionally not part of the manifest taxonomy. Unsupported-host run cases set
`host = "unsupported"` so the manifest runner passes `run --host unsupported`
through the same CLI route users can reproduce.
Run cases may also set `backend = "control-vm"` or `backend = "interpreter"`
to pin backend-specific runtime behavior. Such cases must carry the matching
`backend.control-vm` or `backend.interpreter` tag. The default backend is the
public evidence VM path and usually does not need an explicit backend tag.
`stable-core` marks the Yulang Contract v0 subset described in
`docs/language/stable-core.md`. It is not a synonym for "currently implemented":
do not combine it with `preview`, `migration-canary`, or `compile-error`.
Every `standard-api` case must also be classified as exactly one of
`stable-api` or `migration-canary`. Use `migration-canary` for executable
coverage of current helper spellings or raw surfaces that should not be read as
long-term compatibility promises.
`file-resource` is the Contract v1 file/host resource slice, not part of
Contract v0. Do not combine it with `stable-core`. File resource cases should
use `resource-lifetime` when they observe commit, rollback, handler-extent
discharge, branch-local buffers, or last-write-wins, and `metadata` when they
observe the non-throwing metadata shape. Use `host-act` when a case proves
the public host act protocol itself, including source handlers intercepting host
act operations before the native host registry or native operation failures
becoming typed domain values instead of integer-code bridges.
Runtime cases should declare a host scope: `host.native`, `host.unsupported`, or
`mock-host` plus `host.unsupported` when the mock handler is intentionally run
with native host capabilities disabled. A `mock-host` / `resource-lifetime`
case may also use pure Yulang state to prove the public managed-ref view shape
before the reusable host-backed helper is available.
Contract v1 file protocol-center cases are `stable-api`: public
`load`/`store`/`meta`, `text_with`, ambient `text`, typed file failures,
unsupported-host denial, source mock routing, and their exact public
signatures. Use `raw-compat` for current executable coverage of provisional
range helpers that are intentionally isolated from the Contract v1 protocol
center and should not be mistaken for the final session API; `raw-compat` file
cases remain `migration-canary`.
All `public-signature` cases also reject private evidence and placeholder-like
fragments such as `#...`, `AllExcept(...)`, `Unknown`, and `Any` in the
projected public type. Individual cases can still add narrower
`deny_type_contains` checks for surface-specific leaks.
Each `public-signature` case must also carry an exact `expect_type`; broad
substring-only public type checks are not enough for the contract manifest.
Diagnostic entries may also assert the structured `SourceDiagnostic` payload
with compact fields such as diagnostic count, severity, code, label, primary
byte range, related count, and related origins.
For `kind = "check"` entries, the manifest requires diagnostic count, code,
severity, a complete primary byte range, and related-count assertions so new
diagnostic fixtures cannot silently fall back to message-only coverage.
`run` entries that need native host paths can declare `[[case.temp_files]]`
items. The manifest runner replaces the declared placeholder in the source with
the Yulang string literal for that temp path. Set `contents = "..."` to create a
file and optionally check `expect_contents` after the CLI run, or set
`missing = true` to use a path that is intentionally not created. Use this only
for current executable host behavior; it is not a placeholder mechanism.

`support/fake_std/` contains narrow std shims for tests that need compiler-known
surface paths such as `std::control::flow::sub` but do not need the full public
standard library.

Do not add TODO or ignored placeholders to `cases.toml`. A manifest case is a
current executable contract, not a roadmap entry. Standard API and host
capability cases should enter the manifest only after the native or unsupported
host behavior can be observed through the public CLI.

## Fixture roles

- `regressions/effect/` holds public-signature and handler-hygiene canaries.
  These fixtures protect the solver boundary: public types must not leak
  private stack evidence, and residual effects must not be erased.
- `regressions/runtime/` holds focused public runtime examples. CLI tests run
  these through the normal `yulang` binary with the repository standard
  library.
- `regressions/diagnostics/` holds small invalid programs for compact CLI,
  LSP, and playground diagnostic contracts. These fixtures should each focus on
  one user-facing cause.
- `yulang-adversarial-corpus/` holds broader hardening probes. These are not
  examples for users; they are stress cases for replay termination, handler
  hygiene, and runtime fallback behavior.

Future diagnostic fixtures should keep expected output compact: check the
diagnostic cause, code, label/range, and user-facing message rather than
snapshotting large internal dumps.

Public-surface changes should add or update a manifest case when the change
affects runtime behavior, diagnostics, standard API behavior, or public release
expectations. Keep the manifest compact; broad hardening probes belong in the
adversarial corpus.
