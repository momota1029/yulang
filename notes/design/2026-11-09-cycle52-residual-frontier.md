# Cycle52: exact residual frontier across finite batches

Status: Draft, 2026-11-09. Implementation/proof fragment, not a new language rule.

## Objective and boundary
For any fixed finite source table, initial problem and finite list of updates,
prove that a slot pair belongs to the final packet's pending list exactly when
its named request occurs in the original accumulated input and its receiver is
not forced to str by all independent models of that input. Connect this to
actual checked execution, two inequivalent source models, and successful scope
validation so no original request silently disappears after repeated compaction.

The data and executable driver are unchanged from cycle51. The independent
judgment is the existing SourceModel, quantified over all assignments to the
fixed table. There is no supplied model, acyclicity, or uniqueness premise.
The carrier does not grow; only str seeds, slot type equalities and finite named
requests can be added. This does not close arbitrary generated-role B4.

## Proof plan
Compaction preserves an original named request whenever a source model keeps
its receiver non-str. Propagate that invariant through the finite update list.
Model preservation then identifies final derived receivers with source forcing.
Use the existing independent underdetermination theorem for countermodels.

## Compatibility
Read spec 6.3's equality propagation, delayed finalization and conjunction/order
rules and work/dots-audit notes/audit/x-oracle.md X13–X17 before implementation.
Those finite legacy examples are not an oracle for this internal fragment.
No language-visible classification or dictionary equivalence is chosen here.

## Completed shape
The membership invariant also yields literal equality of the serialized pending
list with a full rebuild. Both lists use the same canonical slot-pair enumeration,
so membership equality suffices without changing the existing execution code.
Reordered finite update batches have the same pending list. Duplicate source
slots remain represented separately; duplicate named request entries are normalized
by the existing pair enumeration. No claim about dictionary or atom-list identity.
