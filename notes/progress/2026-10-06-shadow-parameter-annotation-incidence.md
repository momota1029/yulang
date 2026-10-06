# Shadow parameter–annotation incidence

Date: 2026-10-06
Status: M1 shadow identity slice; independently spec- and regression-reviewed
Baseline: `4b1f6b8d104e639353c7001d7333300e628defa3`
Scope: default-off HIR shadow artifact and `yu-core::shadow` facade
Implementation authority: explicit user authorization for settled source
identity/evidence plumbing; no production inference authority

## Change

The shadow skeleton now exposes `ParameterAnnotationIncidence`, containing an
existing `BinderId` and an existing `AnnotationId`. Its bounded source shape is
an atomic unannotated identifier parameter or a grouped single identifier with
a direct type annotation, such as `(f: T)`. The association follows the exact
CST node, retained artifact-local `PositionId`, and annotation identity. It
does not use spelling, source-range containment, or nearest-descendant search.

Whole-target annotations, expression annotations, and grouped forms outside
that shape remain unassociated/rejected by the skeleton builder; the complete
raw annotation inventory remains available. Existing annotation correspondence
stays `PendingTypedPortAndProfile`. No typed port/profile, `beta`/`Slots(beta)`,
permission, role, admission, `Q`, receipt, or production inference behavior is
derived. All four call premises remain pending, and the selected nested-block
candidate remains outside this extension.

## Review and verification

- `spec_auditor`: no findings; verified exact structural ownership and the
  unresolved typed/profile and semantic boundaries.
- `regression_auditor`: no remaining findings. Its initial minor coverage
  observation led to a two-annotation test with a leading unannotated binder;
  delta review confirmed the test catches binder-zero and annotation-zero
  shortcuts.
- `RUSTC_WRAPPER= cargo test -p yu-hir shadow_annotation_positions --features shadow -j 2 -- --test-threads=1` — 8 passed before the coverage-only delta.
- `RUSTC_WRAPPER= cargo test -p yu-hir shadow_resolved_call_incidence --features shadow -j 2 -- --test-threads=1` — 2 passed before the coverage-only delta.
- `RUSTC_WRAPPER= cargo check -p yu-core --features shadow -j 2` — passed.
- `RUSTC_WRAPPER= cargo test -p yu-hir shadow_annotation_positions_keeps_noninitial_grouped_parameters_distinct --features shadow -j 2 -- --test-threads=1` — 1 passed after the coverage-only delta.
- Targeted `rustfmt --check` and `git diff --check` — passed.

One Cargo process at a time, at most two jobs, one test thread; zero
performance samples. No broad suite, production inference, AST/direct-CST
semantic parity, or performance benchmark was run. The test-only coverage
delta does not change implementation dependencies or behavior.

This closes only grouped parameter/annotation identity plumbing in shadow. It
does not close typed annotation/profile formation, call contract generation,
soundness, principality, source adequacy, or production cutover.
