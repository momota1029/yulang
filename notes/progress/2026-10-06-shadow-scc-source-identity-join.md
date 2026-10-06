# Shadow SCC source identity join

Date: 2026-10-06
Status: implemented in the default-off observer; compiler-referee and regression review complete
Baseline: `5a01fb67e`
Depends on: [parse-branded HIR/shadow identity bridge](2026-10-06-shadow-source-identity-correspondence.md)
Semantic and production-inference authority: none

## Result

The existing borrowed `yu-solver` F0–F2 topology observer now maps each
collection-branded definition/use handle to its retained HIR
`DefinitionRootId`/`HirOccurrenceId`, then asks the HIR source sidecar for the
exact raw-shadow `PositionId`. It reads existing collection maps directly, so
source lookup does not increment query counters. Collection identity,
HIR-artifact identity, parse identity and source-position identity remain
separate checked boundaries with explicit errors.

The `shadow-scc-observer` feature now forwards to the existing `yu-hir/shadow`
feature and remains default-off. No production collection/solve path, SCC
ordering, generalization or inferred expression changed. The bridge does not
join by names, ranges or ordinals and does not require successor skeleton
construction.

## Verification and review

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-scc-observer shadow_scc_observer -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-solver
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver f0_definition_queries_reject_foreign_and_missing_batch_identities -- --test-threads=1
rustfmt --edition 2024 --check crates/yu-solver/src/shadow_scc.rs crates/yu-solver/src/tests/shadow_scc_observer.rs
git diff --check -- crates/yu-solver/Cargo.toml crates/yu-solver/src/lib.rs crates/yu-solver/src/shadow_scc.rs crates/yu-solver/src/tests/shadow_scc_observer.rs
```

The focused feature-on observer suite passes 5/5 after a reverse-DAG coverage
repair. That case confirms the observer's dependency-first definition/use
order differs from source order while expected CST positions are recovered
through exact batch and HIR identities. The independent regression reviewer
closed the ordering-coverage finding. The compiler-referee found no semantic,
ownership or authority-boundary findings. Existing collection and observer
counters remain unchanged in the focused tests.

## Remaining scope

This exposes only current F0–F2 topology identities with exact source positions.
It does not form a successor generalized interface, run a solver, assign Q/R,
freshen schemes, or establish source-rule meaning. Method/role selection,
`beta`/`Slots(beta)`, typed owner/receiver/provenance, soundness,
principality, source adequacy and production cutover remain open. Broad suites,
core/workspace integration, performance measurements and semantic parity were
not checked.
