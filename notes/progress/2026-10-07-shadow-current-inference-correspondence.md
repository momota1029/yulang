# Current inference versus shadow source correspondence

Date: 2026-10-07
Baseline: `649cab5e95e5e191442a6333a5839b231af2b965`
Status: frozen, independently reviewed M1 structural/support-boundary characterization
Claim class: exact source-identity joins on a common leaf subset; unsupported-boundary characterization for applications
Semantic and production authority: none

## Result

The new `yu-core` integration test compares the default-off shadow source
structure with production HIR using one parsed file and the existing explicit
source-identity sidecar. For admitted unary leaf definitions, it checks exact
definition, parameter, and body occurrence joins for both a name use and an
integer literal. It also compares sidecar-enabled HIR with ordinary production
lowering under the existing `HirModule` equality contract.

For ordinary application bodies, current production HIR reports
`UnsupportedExpression` and retains an error body without a source-occurrence
join. The shadow representation separately retains application/use identities
and their pending rows. Two-formal and annotated header candidates are rejected
as `UnsupportedTarget` by production HIR while the shadow projection retains
their ordered header, annotation inventory, and call structure. Grouped and
computed callee controls confirm that direct-use registrations are not
manufactured for those shapes.

This is a source-artifact and support-boundary differential. It establishes no
typing, scheme, role, effect, source acceptance/rejection semantics, old-infer
parity, soundness, principality, source adequacy, or production inference
equivalence. A production `Error` range is not treated as identity evidence for
a shadow application. No Frozen Oracle mechanism or behavior is used.

## Review and repair

The compiler-referee review found no issue in the bounded semantic boundary.
The regression review found a minor test-coverage gap: conditional assertions
could skip registration-membership checks if a registration disappeared. The
primary repaired this by asserting that source-use and root-header membership
are present exactly when a retained direct-use registration is present. This
was a test-only repair. Post-repair focused execution passed; the repair was
then formatted and whitespace-checked.

## Verification

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-core --features shadow --test shadow_current_inference_correspondence -- --test-threads=1` — 3 passed after the repair.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-f5 --test shadow_f5_differential -- --test-threads=1` — 2 passed, reported by the implementer; the test was unchanged by the repair.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo xtask check-graph` — passed, reported by the implementer; the graph was unchanged by the repair.
- `rustfmt --check --edition 2024 crates/yu-core/tests/shadow_current_inference_correspondence.rs` and whitespace/diff checks — passed after formatting.

The new test file SHA-256 at freeze: `6b90c155686c4aebf2ceb1e60ef239fbaf3ef6d6884d67ad2dd04b3a19cdbe04`.
No manifests, dependencies, production paths, fixtures, or existing semantic
expectations changed. Broad suites and semantic inference equivalence remain
unverified.
