# Shadow annotation occurrence and source-boundary plumbing

Date: 2026-10-06
Baseline: `6a44593ef59776cad87180a83111d63d891d0694`
Status: independently compiler-referee-reviewed default-off structural plumbing; test coverage finding repaired
Authority: user's explicit authorization for shadow identity/evidence plumbing with unresolved semantics pending
Semantic authority: none added

## Result

For artifacts with an existing validated `Skeleton`, `RawStructuralArena` now
retains the complete ordered annotation-occurrence list and borrows each
occurrence's exact artifact-owned `Position`. Where the existing HIR records a
`ParameterAnnotationIncidence`, the raw entry retains that exact incidence
after validating its binder and annotation identity against the same artifact.
Repeated or invalid attachments reject the arena before publication. An
occurrence without such an incidence remains present; missing incidence is not
treated as source-level annotation absence. Artifacts without a `Skeleton`
remain unavailable to this raw core arena; their parse-level annotations and
positions remain directly available from `ShadowArtifact`.

The record preserves source identity and its CST boundary, including byte
range and structural parent/ordinal through the borrowed `Position`. The
existing correspondence remains `PendingTypedPortAndProfile`. No beta, static
slot, typed port, profile, annotation permission/removal, boundary effectiveness,
or inference judgment is formed. The production inference path and existing
pending Apply premises remain unchanged.

## Review and repair

A compiler referee found no correctness or semantic-boundary issue, plus one
minor test gap: a one-annotation fixture could not detect reordering or merging
among multiple occurrences. The primary added the existing supported
two-annotation source `my apply x (f: T) (g: T) = f (g x)`, asserting source
order, exact occurrence and Position identities, distinct owner incidences,
and pending correspondence. This test-only repair required no second review.

## Verification

- `RUSTC_WRAPPER= cargo test -p yu-core --features shadow --test shadow_raw_structural_inventory -j 2` — 5 passed after repair.
- `rustfmt --edition 2024 --check --config skip_children=true crates/yu-core/src/shadow_derivation.rs crates/yu-core/tests/shadow_raw_structural_inventory.rs` — passed.
- `git diff --check` on both changed implementation paths — passed.

One Cargo process ran with at most two jobs. No broad suite, Oracle execution,
benchmark, or performance measurement was run. Malformed private incidence
mutation is unavailable through the public constructors; foreign-artifact
rejection is covered.

## Exact limits

This is occurrence/owner identity plumbing only. Annotation interpretation,
typed association, profile formation, protection, call-view registration,
`FVIEW`-to-`SRC`, soundness, principality, source adequacy, production
conformance, and production cutover remain open.
