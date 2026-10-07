# Shadow crosswalk from source uses to receiving current schemes

Date: 2026-10-07
Baseline: `1001c274cbf8bc867a03e72edbbfb08b3618e950`
Status: feature-gated structural characterization; independently reviewed
Gate: HIR_WIRING implementation lane
Semantic and production authority: none

## Result

The new integration test
[`shadow_receiving_root_scheme_crosswalk.rs`](../../crates/yu-solver/tests/shadow_receiving_root_scheme_crosswalk.rs)
uses a generic `id` definition and three public, module-visible and private
aliases. It joins each alias's exact parsed `id` Name occurrence to one
collection-branded incoming use, the target's finalized current scheme and
complete current Q/R capture, then follows the use's receiving parent to its
own finalized alias scheme.

The observer distinguishes the shared target scheme from the three receiving
scheme owners. Each alias retains its `Private`/`Our`/`Public` marker; the test
does not interpret those markers as successor export eligibility. Current Q/R
binders agree across alias uses while each use has distinct fresh row
identities. Reads leave batch and solve counters unchanged. A solve from a
separate collection of the same immutable HIR is rejected by both current-use
and receiving-scheme lookups.

This adds a test-only structural crosswalk. It does not supply an export
product, successor generalized interface, successor Q/R correspondence,
shared-contract transport, source adequacy or production conformance. The
existing unresolved premises are kept explicit in the test:

- `SuccessorGeneralizationRuleUnresolved`
- `CurrentToSuccessorQrCorrespondenceUnresolved`
- `UseTimeSharedContractTransportUnresolved`

No solver or production HIR behavior changed.

## Review and verification

Independent regression-auditor review passed. It confirmed exact parsed source
positions, unique use joins, current scheme ownership, visibility-as-metadata,
disjoint per-use fresh rows, foreign collection rejection and query-counter
purity. Broader resolver, recursive, export, successor and production behavior
were not in review scope.

Focused command:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver \
  --features shadow-f5,shadow-scc-observer \
  --test shadow_receiving_root_scheme_crosswalk -- --test-threads=1
# 1 passed
```

The initial run stopped before compilation because the configured sccache
wrapper returned `Operation not permitted`; the environment-only retry above
passed. The assigned test file was rustfmt-formatted and passed
`git diff --check`. No broad tests, feature-off build, performance sample or
Frozen Oracle execution was run. The test-only shadow slice adds no production
inference behavior and does not authorize cutover.
