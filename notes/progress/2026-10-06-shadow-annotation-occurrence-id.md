# Shadow annotation occurrence identity

Date: 2026-10-06
Status: M2 shadow identity slice; independently reviewed, no findings
Baseline: `cf4ffa4484d701ab85b4f5f9be429a71fe482c33`
Scope: default-off immutable HIR shadow artifact and read-only core facade
Implementation authority: explicit user authorization for settled source
identity/evidence plumbing; no production inference authority

## Change

The HIR shadow artifact now assigns one private-constructor, artifact-branded
`AnnotationId` to every retained `PatternTypeAnnotation` and
`TypeAnnotationTail`. `AnnotationOccurrence::id` exposes that identity, and
`ShadowArtifact::annotation` resolves it with the same foreign-artifact and
missing-reference checks used by other artifact-owned IDs. The `yu-core::shadow`
facade re-exports the type without minting or modifying IDs.

`AnnotationId` identifies a raw source annotation occurrence only. Its
`PositionId` remains the exact raw CST position. Typed port/profile mapping,
`beta`/`Slots(beta)`, permission, owner/receiver evidence and semantic
discharge remain pending. Production HIR, F5 and inference routing are
unchanged.

## Review and verification

- Pre-write `spec_auditor`: no findings. The separate source-occurrence identity
  fits the authorized shadow slice and does not establish profile identity.
- Post-write `regression_auditor`: no findings. IDs are unique in retained
  traversal order; lookup rejects foreign identities; both annotation forms
  remain pending and the facade is feature-gated with no production caller.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-hir --features shadow --lib tests::shadow_annotation_positions -- --test-threads=1` — 6 passed.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo check -p yu-core --features shadow` — passed.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo check -p yu-core` — passed (default feature set).
- `rustfmt --edition 2024 --check crates/yu-hir/src/shadow.rs crates/yu-hir/src/tests/shadow_annotation_positions.rs crates/yu-core/src/shadow.rs` — passed.
- `git diff --check` on the implementation paths — passed.

Cost is one artifact brand/index pair per annotation and one `Arc` clone during
retention. Lookup is constant time; no extra traversal or production work is
introduced. Rollback removes this additive API/storage/tests without changing
the existing shadow artifact behavior. Broad package suites, Oracle behavior
and performance samples were not checked; measurement budget consumed: zero.

This closes only the source annotation identity plumbing slice. It derives no
typed occurrence correspondence, source contract, solver fact, theorem or
production cutover gate.
