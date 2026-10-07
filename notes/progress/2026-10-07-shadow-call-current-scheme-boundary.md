# Shadow Call to current enclosing scheme boundary

Date: 2026-10-07
Baseline: `24d61a2bf6568d560a78b57557b98c2f5cd254b5`
Status: reviewed structural crosswalk; successor use/export remains unresolved
Authority: default-off shadow evidence only
Review: compiler-referee pass; no findings

## Result

The captured local-Call lifecycle test now composes the exact retained
`PendingApplicationOccurrence.enclosing_root` through solve to the current
finalized scheme. With the existing `shadow-scc-observer` feature, it checks
that the same collection's sole SCC definition and component own that root
and scheme. The existing pending marker remains
`SuccessorGeneralizationRuleUnresolved`.

For this exact source fixture, both Apply operands remain absent from solved
occurrence projection, and the joined component has no internal, incoming or
outgoing SCC use records. This confirms there is no operand-to-current-use
fresh-capture route in the fixture. It does not claim a source typing rule,
argument scheme, local `step` scheme, operand instantiation, or successor
generalization.

The fixture's current scheme belongs to enclosing `apply`; it is not the
initializer's local `step` scheme. The source-to-solver Apply row and the
current SCC `DefinitionUseId` collector have disjoint occurrence domains for
these parameter operands. A future-use bridge requires an actual application
and generalization producer that establishes the relevant use and its
transport evidence. IDs, source positions, names, or matching outer roots do
not supply it.

This extends the lifecycle test with an existing observer join. It adds no
production API, constraint, fact, identity carrier, semantic premise
discharge or export path.

## Verification

Both focused checks passed, one test each:

```sh
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver \
  --features shadow-f5,shadow-scc-observer \
  --test shadow_captured_source_retention \
  shadow_local_bind_joins_pending_structural_projection_without_discharge \
  -- --exact --test-threads=1

RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver \
  --features shadow-f5 \
  --test shadow_captured_source_retention \
  shadow_local_bind_joins_pending_structural_projection_without_discharge \
  -- --exact --test-threads=1

git diff --check
```

The compiler-referee reviewed the complete 48-line test delta and relevant
scheme/SCC identity APIs. No broad suite or performance measurement was run.
The current use-freshening route, successor interface formation, publication,
argument typing and source adequacy remain open.
