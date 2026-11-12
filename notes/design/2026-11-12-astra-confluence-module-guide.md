# Feedback executor and refresh divergence: module guide

Item 5b, based on integration `b08ebc485`. The complete theorem statements and
14-field table are in
[Item 5b of the boundary note](2026-11-11-astra-general-boundary.md#item-5b--progress-conditional-executor-and-halted-refresh-divergence).

| Module | Purpose and principal interfaces |
| --- | --- |
| [GeneralDictionaryFeedbackExecutor](../../lean/Yulang/GeneralDictionaryFeedbackExecutor.lean) | `Progress` is precisely the existing V5 field. `exists_halted` constructs a finite trace to a terminal state by Step accessibility. `executor` chooses such a state and reads its diagnostic tree when child accessibility exists. `execution`, `halted`, and the exact `treeExecution` field require only Progress in addition to their original binders. `saturationTotal` composes B4 clause (1) under that same premise. |
| [GeneralNominalTopObservation](../../lean/Yulang/GeneralNominalTopObservation.lean) | `not_known` proves that a model assigning top prevents any certified scalar, normalized structural, or nominal head at that source identity. |
| [GeneralNominalRefreshFork](../../lean/Yulang/GeneralNominalRefreshFork.lean) | A checked `Display (list (list int))` leaf, a source-formed empty journal, and two actual refresh steps. They record a point or wider descriptor for the same known denotation. `same_models` proves both preserve the entire initial model set; `after_models` witnesses nonemptiness. `no_refresh` rules out a later novel Known observation. |
| [GeneralNominalRefreshForkCycles](../../lean/Yulang/GeneralNominalRefreshForkCycles.lean) | The shared model forces all recurrence edges forward through finite source identities. Both raw and journal-aware graphs are acyclic. `not_rootK2` and `not_candidateK2` keep K2 out of the example. |
| [GeneralNominalRefreshForkClassification](../../lean/Yulang/GeneralNominalRefreshForkClassification.lean) | Actual recursive reports and branch constraints: `point_survivor`, `point_branch` in every model, and `wide_inspection_pending` at the unchanged candidate boundary. |
| [GeneralNominalRefreshDivergence](../../lean/Yulang/GeneralNominalRefreshDivergence.lean) | Both endpoints halt. `reachable_halted_divergence` packages the checked initial fork, models, and incompatible diagnostic trees. `child_accessible`, `point_reader`, and `wide_reader` show both results use actual `resolve`, not its total extension's fallback. `no_observational_join` rules out reconciliation. |
| [GeneralDictionaryExecutorOrderResidual](../../lean/Yulang/GeneralDictionaryExecutorOrderResidual.lean) | `HaltedLocalOrder` states the proposed terminal confluence premise. It would supply the executor's exact canonicalLocalOrder field, but `not_halted_local_order` refutes it for the actual Step. `Remaining` retains four obligations alongside the explicit Progress parameter and maps exactly to V5. |

The result is six existing unconditional bridge laws plus three newly proved
laws conditional only on Progress. Progress is assumed, not proved. The four
remaining fields are `whereAccessible`, `canonicalLocalOrder`, `evidenceNode`,
and `generatedChildren`. This is not unconditional B4 completion.

The confluence failure is an implementation gap: refresh can freeze different
model-equivalent interval descriptors, while recursive inspection still depends
on the upper descriptor. No language choice was made, and the recursive
associated-output-growth question and progress/descent remain paused.

New audit part: [Audit/AstraConfluence.lean](../../lean/Audit/AstraConfluence.lean).
The frozen `lean/Audit.lean` and `lean/README.md` remain unchanged.
