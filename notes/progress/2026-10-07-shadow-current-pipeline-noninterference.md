# Current inference instrumentation noninterference differential

Date: 2026-10-07
Baseline: `e8ec553d5ea3e6c3dc02e44523460f5dcb32fa65`
Status: compiler-referee reviewed, focused test passed; shadow-only evidence
Authority: no successor semantics, production behavior, or theorem status changed

## Result

Added one feature-gated differential that independently runs ordinary HIR
lowering and solve beside source-identity HIR lowering and solve with optional
fresh-row capture. For each original declaration, it compares the complete
current finalized scheme using the existing alpha-equivalence observer, while
querying each solve through its own artifact-branded root and occurrence IDs.
This checks that the optional source-identity/capture instrumentation does not
change current inference results on the selected supported fixtures.

Fixtures cover a generic identity with public/our/private receiving aliases, a
productive recursive Function alias, an unproductive recursive alias, and an
integer alias. They exercise nonempty Q inventory and recursive R bounds. The
test also compares diagnostics, occurrence registration and per-occurrence
projections. Nested Lambda bodies use the existing fallback projection; equal
fallback observations are not treated as typing evidence.

## Exact boundary

This is a current-pipeline noninterference check. It does not compare against
the historical inferer, produce a successor scheme or export, type an Apply,
classify callable roles, or prove soundness/principality/source adequacy. It
does not discharge `ApplicationTypingRuleUnresolved`,
`SuccessorGeneralizationRuleUnresolved`,
`CurrentToSuccessorQrCorrespondenceUnresolved`, or
`UseTimeSharedContractTransportUnresolved`. The canonical DAG remains at 90
nodes / 196 edges: CLOSED 7, CONDITIONAL-CLOSED 20, OPEN-PROOF 43,
OPEN-SEMANTIC 19, IMPLEMENTATION-ONLY 1.

## Review and checks

- Independent compiler-referee review: no blocking, major, or minor findings.
- `RUSTC_WRAPPER= cargo test -j 1 -p yu-solver --features shadow-f5 --test shadow_f5_differential source_identity_and_fresh_capture_preserve_complete_current_finalized_schemes -- --exact`: passed (1 test, 5 filtered).
- `git diff --check`: passed for the test change.
- Rustfmt check reports a pre-existing formatting discrepancy at line 676 outside the new test; it was left untouched.
- Broad suites and successor equivalence remain unverified.
