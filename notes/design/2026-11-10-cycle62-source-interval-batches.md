# General source-named interval batches

Status: Draft, 2026-11-10. Scope: B4 source identity and general interval constraint generation.

## Objective and boundary

Close the incremental reconciliation boundary for arbitrary finite batches of source-named interval demands. Each demand stores a source identity and two existing `TyTerm` endpoints. Endpoints may contain every constructor in that existing syntax. Their original type and row slots remain unchanged. The ordinary assignment is not reduced to the positive-string or unary/int fragments.

An independent model gives, for each source name, a mathematical type fitting every interval attributed to that name. This existential value is not stored or chosen by the executable generator. Equal observed types do not identify source names; equal source names require joint reconciliation. The compiler must retain the original assignment, including effect rows.

The generator returns every lower-to-upper comparison within one source group. An incremental step retains old constraints and adds old/new, new/old and new/new comparisons. Omitting the two cross directions would accept two separately valid but jointly incompatible batches. A finite driver consumes arbitrary batches, including repeated source names and duplicate demands. Its complete models must equal reconciliation of the original flattened history. Source order can change the emitted list but cannot change the models.

## Target statements

For every finite request list, ambient assignment, and source name, generated ordinary atoms hold iff there exists a mathematical type fitting all original intervals with that name. For every initial request list and finite list of update batches, the incremental driver has exactly those independent models for the flattened original history. Existing constraints remain conjoined. Compiling that result with the existing shared presence graph has a graph model reading back literally to the same original assignment iff the independent source-interval model and existing constraints hold.

These are generation soundness/completeness results. They do not prove general ordinary solver completeness, graph inspection adequacy, declaration-to-demand generation, recursive syntax allocation, final role classification or B4 itself. In particular this does not disguise the still-open state-dependent materialization bridge as complete.

## Evidence and remaining chain

Before implementation, existing Yulang2 oracle X13–X16 and C3-PARENT were read. They motivate shared-source narrowing; they do not directly validate this compiler. Spec 6.3 and the existing centreless `CommonRoleIntervals`/`CommonRoleIntervalGeneration` semantics remain the authority. No new language decision or rejection rule is introduced. All five general B4 bridges remain open.
