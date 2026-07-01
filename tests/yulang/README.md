# Yulang Regression Fixtures

Small `.yu` files in this tree are shared regression inputs.
Rust tests can load them today, and a future Yulang test runner can reuse the
same files without copying source text out of inline strings.

`support/fake_std/` contains narrow std shims for tests that need compiler-known
surface paths such as `std::control::flow::sub` but do not need the full public
standard library.

## Fixture roles

- `regressions/effect/` holds public-signature and handler-hygiene canaries.
  These fixtures protect the solver boundary: public types must not leak
  private stack evidence, and residual effects must not be erased.
- `regressions/runtime/` holds focused public runtime examples. CLI tests run
  these through the normal `yulang` binary with the repository standard
  library.
- `yulang-adversarial-corpus/` holds broader hardening probes. These are not
  examples for users; they are stress cases for replay termination, handler
  hygiene, and runtime fallback behavior.

Future diagnostic fixtures should keep expected output compact: check the
diagnostic cause, label/range, and user-facing message rather than snapshotting
large internal dumps.
