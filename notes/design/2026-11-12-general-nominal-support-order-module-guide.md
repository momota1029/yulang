# General nominal guarded installation order (Item 4g)

The guarded boundary remains `GeneralNominalSupportBoundary.boundary roles`.
No existing transition or classification definition is changed.

- `Yulang.GeneralNominalReobservationOrder`: derives finite administrative
  accessibility for merge, head refresh, equality feedback, and certified
  descriptor replacement. Point-descriptor facts use source identities, so a
  refresh that changes the slot table cannot reset them.
- `Yulang.GeneralNominalSupportOrder`: proves that formed guarded states have
  registered generated demands, excludes enqueue, lifts administrative
  accessibility to the support ledger, and reduces full guarded accessibility
  to an explicit arbitrary well-founded `InstallationOrder`. It also proves
  full accessibility for formed states with no models.

- `Yulang.GeneralNominalSupportSiblings`: checked P/Container declarations,
  existing Wrap, and an actual first guarded P installation with three emitted
  children and a shared output-only target.
- `Yulang.GeneralNominalSupportRankObstruction`: the relation containing every
  permitted external producer has a two-cycle between generated unresolved
  siblings. This rules out ranking that whole relation. The heads in the
  example also have empty source supports: it is not necessary cyclic support
  or a counterexample to Step accessibility.

The installation order itself is **not constructed**. The conditional
`boundary_progress` is not a closed V5 progress field. See Item 4g in
[the general-boundary design note](2026-11-11-astra-general-boundary.md) for the
measure investigation, exact remaining obligation, and bridge count.

Audit: `lean/Audit/GeneralNominalSupportOrder.lean`. The aggregate audit and
`lean/README.md` remain frozen.
