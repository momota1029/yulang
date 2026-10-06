# Shadow source-call parameter declaration ownership

Date: 2026-10-06
Status: implemented, focused-test verified, independently compiler-referee-reviewed
Baseline: `ac2864a48868b017a8b6fedc6a665f24d0c2daff`
Branch: `research/simple-sub-intrusion`
Authority: user's default-off shadow identity/evidence-plumbing authorization

## Result

The raw shadow core call registration now exposes an optional borrowed
`RawParameterDeclaration` containing the retained Lambda expression and the
exact `BinderId` declared by that Lambda. Construction uses one existing HIR
source crosswalk, then verifies both the crosswalk parameter and Lambda's
parameter equal the call's already resolved binder before publishing the
arena. A missing structural declaration remains `None`; it does not assert
that a binder is not semantically a formal or that its annotation is absent.

The focused fixture checks direct unary calls, repeated uses, the selected
nested captured call (where `f` belongs to the outer Lambda, not local `step`),
and bounded projections whose Lambda declaration is not retained. Foreign
artifact references are rejected. Existing per-call pending rows and
annotation incidences remain unchanged.

## Authority and limits

This adds source ownership plumbing only to the default-off, immutable shadow
artifact. It does not classify a semantic formal, infer annotation absence or
completeness, select callable role, produce beta/Slots, type a Function port,
construct `OriginalAssocType_X`, choose an original `xi`, form a profile,
establish admission/licensing, or discharge any pending premise. Production
inference and F5 are untouched. Soundness, principality, source adequacy and
production cutover remain open.

## Verification and review

The focused check passed:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-core --features shadow --test shadow_raw_structural_inventory -- --test-threads=1
```

Eight tests passed. The initial run had seven passing tests and one fixture
failure because the fixture assumed a multi-parameter projection retained
Lambda declarations. The source inventory showed that it retains the binder
but not that Lambda; the fixture now treats this as absent structural metadata
and does not infer semantic absence. The final run passed.

`rustfmt --edition 2024 --check` on both changed Rust files and `git diff --check`
passed. One compiler referee reviewed the identity joins, nested
capture case, optional absence, atomic publication and feature boundary with
no findings. No broad suite or feature-off build ran. The temporary crosswalk
is linear in the bounded retained artifact and declaration lookups are
constant-time; no performance sample was taken.

Changed implementation paths:

- `crates/yu-core/src/shadow_derivation.rs`
- `crates/yu-core/tests/shadow_raw_structural_inventory.rs`

Next: use retained source declaration ownership only as an identity premise
when deriving the still-open original contribution typing rule; do not promote
it to semantic slot or profile evidence.
