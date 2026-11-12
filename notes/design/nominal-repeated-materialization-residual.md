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

## Additional cycle148 result: point-to-point merge transport

`GeneralNominalRepeatedMergeTransport.merges_iff` proves that the binary
repeated-binder allocation equations are invariant under equivalent endpoint
denotations, even if interval source numbers and the registry differ. The
allocation seed, invocation, declaration, and binder are fixed. This is proved
using join/meet congruence and the actual allocation definitions, not by assuming
equality of the entire generated atom lists.

`point_bounds_equivalent` obtains the endpoint equivalences from old and current
point descriptors of the same nominal source/name and the same model. Both
snapshots constrain one and the same actual observation. Thus equality of
endpoint denotations is a consequence, not an extra assumption, in this family.

`merges_after_steps` combines these facts with an earlier recorded packet and an
actual finite support-transition path. It derives CURRENT merge equations when:

- the earlier and current reports inspect one repeated binary nominal head;
- the declaration has exactly that input binder;
- both old and current parameter intervals are point-valued;
- the nominal source/name and allocation seed agree.

The endpoint source IDs may change; the context/registry need not be identical.
No current merge equation, Joint, Installable, or BranchModels is assumed.
Together with `same_after_steps` and the first section's materialization theorem,
this closes both repeated-head residuals for this covered point-to-point family.
The theorem applies to actual paths including descriptor reobservation; it does
not require that this particular head is the one whose precision improved.

This does not solve the nonpoint-to-point case. Fitting an actual value inside
an old interval does not make the old union-lower/intersection-upper bounds
equal to that value. Replacing those bounds with point bounds can change the
required denotation of an existing allocation origin. General selected-branch
coverage also remains open.

Focused build of `GeneralNominalRepeatedMergeTransport` passed (628 dependency
jobs; one new module built). All six added theorems passed `--trust=0` and axiom
audit; only the standard `propext`, `Classical.choice`, `Quot.sound` occur.

## Integrated fragment theorem

`GeneralNominalRepeatedHistoricalBranch.branch_after_steps` packages the results
as a current `BranchModels` theorem at the caller's SAME assignment. The
hypotheses are an actual support path, an earlier journal packet, the repeated
binary inspection shapes, point old/current parameter bounds, fixed nominal
source/name and allocation seed, and a checked terminal declaration returning
the same head at its source. The current journal model is the only semantic
model premise. There is no assumed SameParameters, merge equation,
materialization predicate, current BranchModels, Joint, or Installable.

Focused build passed (629 dependency jobs; one new module built), and its
`--trust=0` axiom audit lists only `propext`, `Classical.choice`, `Quot.sound`.
This closes the precisely stated covered point-to-point fragment, not general
SameModelBranchAtSelected or any additional general V5 obligation.

## Arbitrary finite merge congruence

`GeneralNominalMergeCongruence.merges_iff` removes the binary/single-binder
restriction from the equation-transport algebra. An ordered `All₂` relation
requires identical corresponding binder names and equivalent corresponding
lower/upper endpoint denotations. The theorem preserves the computed merge
equations under a stable seed/invocation/declaration; registries and interval
source numbers may differ. All finite lengths, absent declared binders,
singleton occurrences, and arbitrarily repeated names are covered. No
injectivity, point bound, or special declaration.inputNames premise is used.

`occurrences_equivalent` proves filtering preserves the paired relation.
`lower_equivalent`/`upper_equivalent` derive n-ary join/meet denotation equality.
`mergeAtoms_iff` handles each name's empty/singleton/repeated cases, including
its actual allocated capture identity. `ofFn_merges_iff` provides a Fin n
interface for the shared-name inspection family.

Focused build passed (629 dependency jobs, one new module built); all seven new
theorems passed trust=0 axiom audit with only standard axioms. This algebraic
transport alone does not establish endpoint equivalence after arbitrary
nonpoint refinement or journal coverage for newly selected declarations.
