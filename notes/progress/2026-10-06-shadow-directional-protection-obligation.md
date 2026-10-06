# Pending shadow obligation for directional formal protection

Date: 2026-10-06
Status: reviewed shadow plumbing; no semantic discharge or production authority
Local baseline: `9dcc43ad8`
Selected rule record: upstream commit `e6a77859e5aed22338016c38ea520c0ee3d069c1`,
`notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` §§1–6

## Selected direction and proof boundary

The direct user correction selects a directional local rule: while an
unannotated inferred formal is protected as a variable, an original source
upper Function use protects that view's covariant output-effect occurrence.
That protection does not flow backward to an existing provider/recursive
Function lower effect. Independent lower protection remains intact. The rule
does not mark every effect in a completed Function or latent result, infer
from normalized type shape, or wait for the Function comparison `Q`.

The accompanying source-generation derivation was independently reviewed by a
compiler referee and a spec auditor. A narrow run of its frozen finite checker
passed with 32,768 direction/join instances, 32,768 order checks, 256 joint
relations, 768 query-filter checks, and the named mutants rejected. The checker
consumes certified seed and upper-exposure records; it does not parse source or
prove that all source exposures were generated.

Still open are source-wide seed and upper-exposure construction, exact typed
output-effect correspondence, original scope and whole-`xi` transport,
contribution/receipt/receiver realization, full original-solution preservation,
principality, admission, source adequacy, and production Option A/2 conformance.
No Oracle semantics were used as authority. The prior exact singleton
`Applicable_original -> p0` is not the current unconditional target after this
direct correction; complete enumeration of source-justified directional
exposures is the remaining source-generation obligation.

## Shadow implementation

The default-off HIR shadow adds
`SourceDirectionalOutputEffectProtectionIntroduction` alongside the existing
formal-use applicability stub for each direct resolved-Use application. Each
record retains the existing branded application `ExprId`. It only states that
the directional rule's seed applicability, source upper use, exact typed
output occurrence, original scope and joint assignment still need evidence.
It asserts no protection, formal status, annotation absence, profile member,
no-backflow result, `Flow`, receipt, admission, or semantic acceptance.
Grouped/computed/integer callees remain excluded, and repeated calls retain
distinct occurrence identities.

The obligation's exact pending inventory is reflected in sibling tests. The
16,000-record direct-projection case is unchanged because it bypasses the final
source-stub augmentation. The pending-variant and inventory changes received
one exact-conformance review; the review repair changed only those expected
pending counts/arrays.

Checks:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow --lib shadow_ -- --test-threads=1
# 32 passed
rustfmt --edition 2024 --check --config skip_children=true \
  crates/yu-hir/src/shadow.rs \
  crates/yu-hir/src/tests/shadow_call_use_source_inputs.rs \
  crates/yu-hir/src/tests/shadow_annotation_positions.rs \
  crates/yu-hir/src/tests/shadow_call_source_occurrences.rs \
  crates/yu-hir/src/tests/shadow_source_core.rs \
  crates/yu-hir/src/tests/shadow_resolved_call_incidence.rs
git diff --check -- \
  crates/yu-hir/src/shadow.rs \
  crates/yu-hir/src/tests/shadow_call_use_source_inputs.rs \
  crates/yu-hir/src/tests/shadow_annotation_positions.rs \
  crates/yu-hir/src/tests/shadow_call_source_occurrences.rs \
  crates/yu-hir/src/tests/shadow_source_core.rs \
  crates/yu-hir/src/tests/shadow_resolved_call_incidence.rs
```

This slice changes only default-off shadow bookkeeping. It does not change
production inference or prove the selected rule for arbitrary source graphs.
