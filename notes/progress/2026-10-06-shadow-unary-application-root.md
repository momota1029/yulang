# Shadow unary declaration root for ordinary application

Date: 2026-10-06
Status: default-off shadow structural slice; compiler-referee and regression review complete
Baseline: `a9e719cbde76e210c6023e648826da65de6f0ebb`
Implementation authority: explicit user authorization for settled shadow
structure/identity/evidence plumbing; no production inference authority

## Change

The direct-unary `my` declaration root now also wraps exactly one existing
ordinary Apply when both callee and argument are direct `Use` or
`IntegerLiteral` expressions. Covered source shapes include ML application
(`my f x = x x`, `my f x = 42 x`) and CallTail application
(`my f x = x(42)`, `my f x = 42(42)`). Existing direct identifier/integer body
projection remains unchanged. The declaration binder is still appended only
after body projection; `Skeleton::body()` returns the original Apply; captures
remain empty; declaration scope validation runs before artifact publication.

Each retained Apply keeps all four existing pending premises: callable role,
complete Function membership, call-view realization, and Q-independent source
call-view formation. No premise is discharged. The tests distinguish callee,
argument, call-tail, nested Apply and Group source positions and preserve the
declaration/parameter identity relation. Grouped operands, nested/repeated
application chains, multiple formals, `our`/`pub`, and captured block forms do
not receive this declaration wrapper.

This is source identity and incidence only. It gives no callable type/effect,
role, `beta`/profile, receipt, admission, typed owner/receiver, inference
result, or production source acceptance. Production HIR/F5 and inference
routing are untouched.

## Review and verification

Compiler-referee review found no blocking, major, or minor issue in the code
delta. Regression review's optional coverage finding was closed by explicit
assertions for integer callees and nested/Group CallTail arguments; a fresh
delta review found no remaining issue.

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow shadow -- --test-threads=1` — 36 unit and 1 integration test passed.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow shadow_source_core_unary_ -- --test-threads=1` — 3 tests passed after the delta.
- `rustfmt --edition 2024 --check crates/yu-hir/src/shadow.rs crates/yu-hir/src/tests/shadow_source_core.rs` — passed.
- `git diff --check` — passed.

The branch adds at most one declaration binder and Lambda for an admitted
single-Apply body. No production hot path or performance sample is involved;
zero samples were taken.

## Remaining gates

The current production lowerer still rejects ordinary expression applications
at its atom-only `lower_simple_chain` seam. This shadow slice does not claim a
successor/current-infer differential for call semantics. Complete call-view
formation, typed incidences, receipt and receiver, independent admission,
soundness, principality, source adequacy, and production cutover remain open.
