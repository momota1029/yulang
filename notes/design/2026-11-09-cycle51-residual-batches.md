# Cycle51: residual continuation with finite batches

Status: Draft. 2026-11-09. Scope: finite positive str/equality fragment only.

## Goal and independent contract
For any finite source table T, initial problem P (str seed slots, slot equalities,
named conditional Index requests), any finite list of update problems U, and any
assignment a of Common types/effects to all slots, prove:

`SourceModel (advanceMany P U) a ↔ SourceModel (appendMany P U) a`.

Each advance retains previously derived str slots and only unresolved requests,
then appends the batch's seeds, equalities, and newly introduced requests. The
right side is the independent source clauses of every original batch, without
saturation in its definition. This handles later equality information and new
finite obligations, not just later str seeds. Neither side requires a supplied
model, distinct source names, acyclicity, or a fixed number of update rounds.

## Data and proof route
`Problem T` holds the three existing input lists. `compact` keeps computed facts
as seeds and projects residual occurrence pairs to names. `append` joins every
clause list. Source-model conjunction is exact for append; the existing residual
retention theorem makes compact model-equivalent. Induction on batches then
proves the main iff. Build the final residual packet with the existing driver;
transfer checked success and pending readout through the model iff.

The checked entrance validates the full accumulated original request names,
not only compacted names. Thus a missing source name cannot disappear as a side
effect of compaction. Keep the existing missing-list order and duplicates.

## Specification and boundary
Spec 6.3 says ordinary associated-type equalities can arrive later and siblings
are recomputed until stable (lines 88, 95, 132-133). The existing Yulang2 x-oracle
X13-X17 is read as limited evidence, not a proof of this internal carrier.
No new language rule is chosen. This is a fixed finite source table and finite
provided update list, not source parser lowering, unbounded generated-child
closure, general Paterson termination, four-way classification, or principalness.
The five general B4 bridges remain open even if this subgoal closes.
