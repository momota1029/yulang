# Yulang Regression Fixtures

Small `.yu` files in this tree are shared regression inputs.
Rust tests can load them today, and a future Yulang test runner can reuse the
same files without copying source text out of inline strings.

`cases.toml` is the public contract manifest. It names the small fixtures that
currently define the executable language floor for CLI runtime, diagnostics,
runtime error, compile error, and public signature behavior. Each entry should
point at a focused `.yu` file and list the contract tags it protects.
The manifest runner checks that `run` cases carry a runtime-facing tag, `check`
cases carry `diagnostics`, and `public-signature` cases carry
`public-signature`, so the tags remain useful as a contract index rather than
free-form notes.
`runtime-error` cases must set `expect_success = false`; `public-example` cases
must point at `examples/` from the repo root; and `standard-api` cases must name
a narrower API area such as `result`, `errors`, `path`, or `file`.
All `public-signature` cases also reject private evidence fragments such as
`#...` and `AllExcept(...)` in the projected public type. Individual cases can
still add narrower `deny_type_contains` checks for surface-specific leaks.
Diagnostic entries may also assert the structured `SourceDiagnostic` payload
with compact fields such as diagnostic count, severity, code, label, primary
byte range, related count, and related origins.

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
