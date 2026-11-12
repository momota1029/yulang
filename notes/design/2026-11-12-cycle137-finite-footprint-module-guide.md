# Cycle137: finite descriptor footprints and actual refresh replay

This supplements `2026-11-12-cycle137-current-context-replay.md`. Frozen
`lean/Audit.lean` and `lean/README.md` are untouched (I-24).

## Source, not evidence, conditions

`GeneralDictionaryInspectionLocality` computes a finite descriptor-read footprint
from the actual recursive query and source bounds. Nominal queries include both
endpoint descriptors and recursive type arguments; structural queries recurse
through the normalized view's child bounds. A variable query has empty footprint:
capturing a bound does not inspect the value or its descendants. The footprint is
conservative, not minimal (it includes some mismatched/unvisited branches).

With the entire normalized view fixed and nominal descriptors equal only on this
footprint, `inspect_local`, `inspectMany_local`, and `report_local` prove full report
preservation, including captures, intervals, anchors and tests. This is not an
assumption of report equality, candidate selection, Instance or Evidence.
`FootprintAt` gives a node-local adapter; children are evidenced at the new context.

`GeneralDictionaryRefreshDescriptors` proves an actual same-carrier refinement's
slot embedding is identity using source injectivity, and its nominal-preservation
field retains every old `some` descriptor. No assertion is made about old `none`.

`GeneralDictionarySelectedLocality` narrows the guard further to the payload's
selected declaration key. No report-preservation premise is imposed on other candidates of that role;
actual refinement still retains all old populated descriptors.
`OccupiedFor` asks that the finite inspected slots already contain descriptors.
Actual refinement derives the footprint equality from occupancy, and then the
current Instance. Occupancy is sufficient, not necessary; scalar/absent-descriptor
queries may instead use the equality-based footprint adapter. No claim says all
stable states satisfy occupancy or fixed-view reobservation.

The concrete recorded-parent example discharges occupancy and uses the real
journal refresh. It has an actual model and a child whose descriptor changes.
That child is K2-rejected: the result is a local parent Instance, NOT a complete
recursive dictionary for a rejected child.

## Actual journal paths

`GeneralDictionaryRecordedRefresh` obtains historical packet Instances from
SourceFormed and transports them across ordinary extension, certified refresh,
and any ordinary feedback tail. The refresh model-equivalence theorem supplies
the middle model; no new Joint hypothesis or substituted existential model occurs.

`GeneralDictionaryRefreshTrace` permits finite interleavings of ordinary feedback
and reobservations carrying both an actual feedback Step and a node-local report
certificate. `trace_feedback` proves it is an actual feedback trace. The final
model is pulled backward along those real steps, and the same parent key and
ordered children survive in the final context. This is a restricted trace theorem,
not a constructed general executor or unconditional refresh enablement.

## Still missing

B4SkeletonV4 remains **8/13 unresolved**. In particular evidenceNode is not closed:
we still need stable selected nodes to be recorded compatibly, and general
inspection/refinement transport (changing normalized views and/or source carriers)
without the present guards. Exact dictionary witness transport does not imply
selection stability, canonical execution, or source-compilation coverage.

Next focused proof candidates:
1. Derive selected-key footprint preservation for finished supported inspections
   under general checked refinement, transporting source indices explicitly.
2. Connect actual stable selection to a compatible recorded packet in every final
   model, without replacing stability or adding a desired Evidence conclusion.
3. Connect refreshed/generated child evidence to actual stable selections at the
   one final context. `GeneralDictionarySelectedTree` now transports the exact
   finite witness using only the selected key at each observed node; it also
   derives this from actual refinement and occupied selected footprints, and
   proves the guard invariant under DictionaryEquivalent.
