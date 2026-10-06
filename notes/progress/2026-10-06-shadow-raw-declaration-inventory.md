# Shadow raw source declaration inventory

Date: 2026-10-06
Status: implemented, focused checks passed, spec-auditor reviewed; shadow-only
Baseline: `0f03fb9cfbd48a615b0d2ec08eda02a3ad2f33b4`
Authority: user authorization for default-off shadow structure/identity plumbing; [shadow promotion gate](2026-10-06-shadow-core-promotion-gate.md)
Production inference authority: unchanged

## Slice

`ShadowArtifact` exposes lazy `raw_declaration_positions()` and
`raw_identifier_expression_positions()` readers over its existing retained
CST positions. The first returns direct-root `BindingStatement` occurrences
in source order, independently of narrow `skeleton()` success. The second
returns exact identifier-expression occurrences in retained source order.
Callers can inspect declaration children to reach header, pattern, name and
body positions.

The readers reuse existing artifact-branded `PositionId`s. They add no retained
state, grammar support, resolver result, component/SCC membership, `UseId`,
type or effect judgment, Q/R binder, profile, typed receipt, owner/receiver
evidence, solver call, or production inference route. Identifier resolution
and classification remain pending. Nested bindings are not promoted to
direct-root declarations.

## Evidence and review

Three focused tests cover declaration order and children on a source whose
narrow skeleton is unsupported, duplicate identifier occurrences with
distinct positions and artifact-brand rejection, and exclusion of nested
bindings from the direct-root declaration inventory. Independent
spec-auditor review found no blocking, major, or minor findings. Review covered
the frozen two-file implementation/test delta and the shadow promotion gate;
it did not certify inference semantics or production behavior.

Verification:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow raw_source_inventory -- --test-threads=1
rustfmt --edition 2024 --check crates/yu-hir/src/shadow.rs crates/yu-hir/src/tests/shadow_raw_source_inventory.rs
git diff --check -- crates/yu-hir/src/shadow.rs crates/yu-hir/src/tests/shadow_raw_source_inventory.rs
```

The focused test command passed all three tests. Formatting and diff checks
passed. One Cargo process with two build jobs was used; no performance samples
were taken. Broader HIR/core checks and production tests were not run.

## Remaining boundary

This retains raw declaration/use source origins for later correspondence work;
it does not expose resolved recursive components, classify source uses, or
construct generalized SCC interfaces. Q/R identity, source-to-typed
correspondence, call-view/profile generation, source adequacy, soundness,
principality and production cutover remain open.

`tasks/current.md` synchronization is deferred because that shared path has an
unresolved staged reverse diff from its committed version. The primary did not
overwrite or include that state. The primary committed only this slice's two
implementation/test files and this note in `4108a8fdb`; no branch rewrite or
push was performed.
