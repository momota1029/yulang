# Repeated nominal materialization and journal transport

Status: proved local lemmas; general V5 `SameModelBranchAtSelected` remains open.
Cycle: 148 (2026-11-12).

## Exact advance

`GeneralNominalRepeatedMaterializationFacts.schema_models` derives the entire
materialization predicate for an actual nominal head with the same binder in
both argument positions. It quantifies over arbitrary states, assignments,
nominal descriptors, and interval endpoints. There is no point-interval
restriction and no injectivity/distinct-binder premise. Its genuine semantic
premises are the original state model, equality of the two actual observations,
and the allocated merge equations. Both values fit the merged interval by the
existing union-lower/intersection-upper theorem; all variable/coherence tests
are proved.

`branch_models_iff` combines this with actual inspection and request generation.
For a checked terminal declaration with one associated equation producing that
same repeated head at its existing source identity, branch validity is exactly:

1. the original source state model;
2. equality of the two observed parameters in that same assignment;
3. the computed allocation merge equations in that assignment.

The old independent `GeneralNominalMaterialization.Models` residual has been
removed for this scope. A nonempty associated request is handled. No claim is
made about arbitrary output identities or nonterminal where-clauses.

## Actual history, not an Installable wrapper

`GeneralNominalRepeatedJournalFacts.same_after_steps` recovers repeated-parameter
equality from a packet actually present in an earlier journal. It follows any
finite sequence of the actual support transition relation and uses the caller's
current model throughout. It does not assume Joint, Installable, Committed, or
current BranchModels. Backwards model preservation supplies the old journal
packet's constraints.

`projection_after_steps` then derives the current repeated projection under a
current descriptor at the same source/name. Its current interval bounds and
binder name may differ from the earlier ones. Thus descriptor reobservation
does not require unchanged interval syntax for transporting observed equality.
This result only needs an actual path and packet membership, not an artificial
assumption that all selected branches already hold.

## Remaining exact obstacles

These results do not establish that every current selected declaration has a
suitable earlier journal packet. A newly selected, uninstalled declaration is
not covered. Calling `stable_committed` cannot supply this coverage for free:
its Installable premise already requires the unresolved Joint condition.

Even with historical coverage, a changed report can compute different
union/intersection bounds. The old packet asserts the old merge equations.
Observed parameter equality and fitting both old/new intervals do not alone
identify their join/meet denotations. `ReobservationSteps.Certified` preserves
journal models and refines raw state models; it does not state equality of all
old and new interval endpoints or of their computed merge expressions. The
current allocation equations therefore remain a genuine separate obligation.
No unconstrained-source reassignment, fresh model, or assumption of the target
conclusion was used to hide this difference.

## Verification

Focused `lake build Yulang.GeneralNominalRepeatedMaterializationFacts
Yulang.GeneralNominalRepeatedJournalFacts` passed (627 dependency jobs; two new
modules built). `lake env lean --trust=0` with `#print axioms` for all four new
theorems passed. Dependencies are only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, new axiom, or `native_decide`; no existing semantics,
V5 target, aggregate Audit, or frozen README was changed. This is not a full
package build or general V5 completion claim.
