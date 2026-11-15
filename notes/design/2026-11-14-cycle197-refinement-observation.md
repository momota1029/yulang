# Cycle197 follow-up: old-only nominal observations

The first inspection-trace checkpoint proves actual report transport for scalar,
structural and nominal successful finite traces. Structural traces allow different
old/new head-kind indices when their shapes and ordered child slots agree.
Deferred/failed queries have no trace constructor.

The next bridge is stronger for nominal patterns: an actual source-preserving
`Refines old (replace old next)` cannot change a previously present nominal
descriptor. The source map remains identical and is injective, forcing its slot
embedding to be identity. Descriptor renaming by identity then preserves the
entire declaration and argument list. Thus the earlier design's warning about
arbitrary used-descriptor modifications concerns unconstrained Views, not these
certified same-slot refinements.

`Observed`/`ObservedMany` record successful observations of the old state only.
They cover variables, point nominal queries and both endpoints of nonpoint
nominal queries, recursively. `TreeObserved` restricts this to actual used keys
and argument lookups of one finite complete dictionary. An actual WF refresh
certificate automatically discharges every next-descriptor premise of the first
checkpoint; no new report agreement or semantic Evidence conclusion is included
in the observation condition.

A concrete nested nominal dictionary has constructed source Instance and complete
readback evidence in every old model, including private replay, projection and
request-schema checks. The all-final-model theorem now obtains its destination
trace solely from the actual refresh certificate. A nonpoint interval regression
covers both endpoints. The earlier executable fixture provides genuine WF Step
and an inhabited model; no Initial/Reachable theorem is asserted.

Remaining limitation: successful old nominal observations and the source complete
dictionary still must exist. Scalar/structural observations are not automatically
preserved by this refinement theorem; they retain the first checkpoint's explicit
local shape/head conditions. Arbitrary newly selected nodes and all step branches
of the general WF/V6 EvidenceNode obligation remain open. No general completeness
or consistency theorem is claimed.

## Final strengthening: recover observations from actual completed inspection

`GeneralNominalFinishedObservation197.Syntax` is the syntax-only subset generated
by variables and nominal constructors with recursively admitted children.
For every state, admitted query, bounds and origin, `observed_of_finished` proves
that `Finished (inspect ...)` implies an old-only `Observed` tree. Its mutual
list theorem handles exact arity, both endpoints of nonpoint intervals, and
append completion. Deferred/scalar/structural queries are not admitted by Syntax.

`GeneralNominalSyntaxRefresh197.node_transport` extracts this Finished fact from
the actual source Instance, rather than asking for it separately. For every
registry whose translated input queries satisfy Syntax, old context, same-slot
View, actual Refines, assignment satisfying the new state, and complete old
source Instance, it constructs the corresponding new Instance with the identical
key, children and assignment. Tree/evidence transport keeps the entire readback
payload, including canonical children and multiplicity, not just an erased key.

`universal_refresh` quantifies over every actual WF refresh certificate of this
same-slot form and every final model. Assuming complete old evidence in every
old model and the syntax check, it produces the identical complete payload in
every final model. Old source witnesses may depend on the model. There is no
uniform-witness, TreeObserved, descriptor-agreement or report-equality premise.
Source evidence remains a necessary preservation input, not a newly proved
producer for arbitrary selected nodes.

## Module guide

- `GeneralNominalInspectionTrace197`: exact actual report transport for finite
  successful local observation traces; scalar, structural and nominal cases.
- `GeneralNominalTraceDictionary197`: finite dictionary trace bridge to the
  unchanged actual WF refresh relation, same model and complete payload.
- `GeneralNominalTraceRefreshExample197`: actual descriptor-changing step and
  nested nominal trace; changed slot0 outside the inspected slots1/2.
- `GeneralNominalTraceEvidence197`: constructs the concrete old complete nested
  evidence (including private/projection/materialization obligations), transports
  it universally, and proves model inhabitance.
- `GeneralNominalRefinementTrace197`: source injection forces identity embedding;
  actual Refines automatically retains nominal descriptors and old traces.
- `GeneralNominalRefinementExample197`: old-only nested observations and nonpoint
  interval regression, both endpoints inspected.
- `GeneralNominalFinishedObservation197`: actual completion plus syntax implies
  the old observation certificate, with no semantic evidence hypothesis.
- `GeneralNominalSyntaxRefresh197`: strongest general preservation theorem above;
  derives observations from actual source Instance completion.
- `GeneralNominalSyntaxExample197`: concrete syntax-only all-final-model complete
  payload, inhabited final model, and deferred-query exclusion regression.

The concrete witness has no generated child obligations and has two nested
nominal input constructors. Its focus occurrence is distinct from the active
refresh root; this intentionally tests preservation away from changed slot0,
not production of evidence for that newly materialized root. General slot-growing
refinements, arbitrary mixed syntax automatic preservation, and the remaining
EvidenceNode branches are not proved here.
