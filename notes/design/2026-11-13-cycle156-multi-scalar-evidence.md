# Cycle156: multiargument scalar heads from current syntax

Draft proof design, 2026-11-13. I-25 evidenceNode soundness lane.

The current provenance pipeline restricts its scalar alternative to one point
argument. Extend this to an arbitrary finite list of point scalar arguments;
inputNames remains empty, no nominal descriptor is permitted at these slots,
and each translated query must match its current scalar observation. Source
identities may repeat. This is not arbitrary interval or capture support.

Prove inspectMany/report exact by list induction, with empty captures/projections
and reflexive self-checks. Then derive current BranchModels and Instance from
actual reachable request provenance. This certificate contains syntactic head
facts, not all-model branch validity. Lift to the existing selected-node rule and
recursive payload soundness without changing any classifier or Step definition.
Generic coverage derivation and V5 evidenceNode remain open.

## Root-only nonpoint extension

The original InitialSource already requires each root argument's lower value to
be below its upper value in every initial model. Actual Value steps preserve
models backwards. Therefore these inequalities need not be assumed again at a
reachable current state. Prove locate reconstruction to identify current carrier
slots with the unchanged source demand endpoints. Use arbitrary scalar lower
heads with no upper-head test: exactly the existing inspect rule. This permits
nonpoint roots without changing semantics. Descendant initial interval invariants
are not asserted; the extension is explicitly restricted to the original root.
