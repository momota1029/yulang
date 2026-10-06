# Resolved call-use incidence in shadow HIR

Date: 2026-10-06
Status: default-off identity-plumbing slice; independently compiler-referee-reviewed with no findings
Baseline: `f1fc1a6eb700b1406d6bedebb46aec7cad082774`
Implementation authority: explicit user authorization for settled shadow structure/identity plumbing; no production inference authority

## Change

`Skeleton::resolved_call_incidences()` lazily filters the existing
`ApplicationSourceOccurrence` scan to applications whose direct callee is
already a resolved `Form::Use`. Each result exposes the unchanged Apply
expression, source position/form and argument, plus that existing use
occurrence's `UseId` and resolved `BinderId`.

The focused source `my f x = x(x x)` retains two nested Apply expressions whose
callee uses share one binder while keeping separate use and Apply identities.
Integer-literal callees are filtered from this use-incidence iterator while
remaining in the ordinary application inventory. Grouped and computed callees
are not traversed to invent a direct-use identity.

This does not group or aggregate uses, create a call contract or profile,
construct typed paths/receipts/owners/receivers, classify callable roles, or
discharge any premise. Each Apply retains all four existing pending call
premises. Production HIR/F5 and inference routing are unchanged.

## Verification and limits

Checks passed:

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow --lib shadow_resolved_call_incidence -- --test-threads=1` — 2 passed.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow --lib shadow_call_source_occurrences -- --test-threads=1` — 3 passed.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-core --features shadow` — passed.
- `rustfmt --check --edition 2024 --config skip_children=true` on the four changed Rust paths; `git diff --check` — passed.

Independent compiler-referee review found no blocking, major or minor issues.
The iterator adds no retained graph; it scans O(expressions) with constant
auxiliary storage. It does not establish F5/Oracle parity, semantic role
aggregation, source admission, typed correspondence, soundness, principality,
or source adequacy. No performance samples were taken.

## Commit packet

- Exact paths: `crates/yu-hir/src/shadow.rs`,
  `crates/yu-hir/src/tests/shadow_resolved_call_incidence.rs`,
  `crates/yu-hir/src/lib.rs`, and `crates/yu-core/src/shadow.rs`.
- Implementation commit: `d073264c0`.
- No changed semantic dependencies; production inference untouched.
- No broad suite or runtime differential was run.
