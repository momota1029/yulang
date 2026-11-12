# Cycle148: the revised emission gap is not a stable endpoint

The cycle147 `GeneralDictionarySupportGeneratedChildrenRegression` revision
example proves a reachable, modeled snapshot whose current syntactic emission
is absent from the historical generated graph. It does **not** refute the
stable V5 `GeneratedChildren` obligation.

`GeneralDictionarySupportRevisionStability.lean` now proves why: a second
certified reobservation at source slot1 is still enabled. Slot0 was already
changed from the interval `(2,3)` to `(2,2)`; slot1 still has the old interval.
The source ordinary equations identify endpoints2 and3 in every model, so the
second replacement preserves the complete journal model set in both directions.
It strictly improves the existing point-observation measure. `remaining_update`
is an actual support `At` at the generated root, and `not_stable` contradicts
`Stable` directly with that enabled update.

The continued state `pointFinish` is source-reachable by a third actual support
step. `point_models_iff` proves model equivalence for **every** assignment, not
only the concrete inhabited witness. `point_closed` proves all stored nominal
descriptors now have point parameters, and `no_further_point_revision` excludes
further updates of this limited precision rule. However `point_emission_gap`
shows the same missing current child remains: point precision alone does not
repair the historical graph. This state is not claimed globally stable, and
no current selected judgment is claimed for either snapshot.

These are concrete operational facts, not a discharge of general V5.
General binding-changing stable selection, general Joint, and the general
GeneratedChildren residual remain open. No existing boundary, transition,
semantics, aggregate import, or audit file is changed.

Validation: focused Lean4.35.0 `--trust=0` elaboration succeeds. The new module's
key exported theorems were individually `#print axioms` audited; only
`propext`, `Classical.choice`, and `Quot.sound` occur. No sorry, native_decide,
or new axiom is introduced. No full project build was run.
