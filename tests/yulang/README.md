# Yulang Regression Fixtures

Small `.yu` files in this tree are shared regression inputs.
Rust tests can load them today, and a future Yulang test runner can reuse the
same files without copying source text out of inline strings.

`support/fake_std/` contains narrow std shims for tests that need compiler-known
surface paths such as `std::control::flow::sub` but do not need the full public
standard library.
