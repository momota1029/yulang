# Default-off current use-route crosswalk

Date: 2026-10-07
Baseline: `f3be02da1ba169a88acc154ac29621634f3cc89b`
Status: M1 shadow evidence-plumbing slice; independently compiler-referee reviewed
Authority: user's approved experimental shadow lane; current implementation evidence only
Review: compiler_referee PASS; exact three-file diff, no findings

## Change

The existing pending SCC-use observer joined a retained use to its target,
component, finalized current scheme and opt-in current Q/R capture. It now also
borrows that exact use's retained current route from the same `SolvedModule`:
route kind, owning-store fact when present, and provenance edges for that route.
Collection identity is checked before lookup. No cross-store `FactId` comparison,
route registry, solver mutation, or counter update is introduced.

The outer `Option` distinguishes no committed route from a committed
`IncomingBottomTrivial` route whose fact and provenance are absent. Existing
pending successor-generalization, current-to-successor Q/R correspondence, and
use-time shared-contract transport remain unresolved. No source typing,
original `beta`/`Slots`/owner association, admission, or export fact is inferred.

## Differential evidence

The focused receiving-root test now covers three source aliases joining exact
incoming uses to structured routes, same-store facts and source provenance,
while ordinary and capture-enabled solves agree on route kinds and provenance
coverage. A second fixture covers an integer incoming route. A mutual-recursive
Bottom fixture covers internal routes and the factless Bottom-trivial incoming
route. Foreign collection lookup is rejected and observation leaves solver and
collection counters unchanged.

## Checks and review

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver \
  --features shadow-f5,shadow-scc-observer \
  --test shadow_receiving_root_scheme_crosswalk -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo check -p yu-solver
rustfmt --edition 2024 --check --config skip_children=true \
  crates/yu-solver/src/shadow_scc.rs \
  crates/yu-solver/tests/shadow_receiving_root_scheme_crosswalk.rs
git diff --check -- crates/yu-solver/src/lib.rs \
  crates/yu-solver/src/shadow_scc.rs \
  crates/yu-solver/tests/shadow_receiving_root_scheme_crosswalk.rs
```

The focused test passed 2 tests; the feature-off package check, targeted
formatting and whitespace checks passed. The initial test attempt exposed an
invalid comparison of term handles from separate solves; the test now compares
only within-store identities and cross-run route/provenance coverage. The
compiler-referee independently reviewed ownership, identity, factless-route
distinction, feature gating, observer purity and the focused tests with no
findings. No broad suite, performance measurement, or production inference
change was made.

The explicit observer scans retained routes and provenance only when called;
no retained state or allocation is added. The absent committed-route branch
has no direct finalized-scheme source fixture yet. `HIR_WIRING` remains
IMPLEMENTATION-ONLY, and all semantic DAG counts remain unchanged.
