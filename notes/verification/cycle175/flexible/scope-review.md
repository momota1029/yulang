# Independent review: cycle175 recursive completion and refresh

## Completion175

No material scope issue found in the source review.

- The source journal is initialized empty through InitialSource. The explicit
  path uses GeneralDictionaryAgreedRefiningTrace174.Step, not an invented
  semantic edge predicate containing Instance/Evidence.
- The same final assignment is passed to every node and child of Classify.
  Neither a fresh model per branch nor an existential branch model is used.
- Generated closure of selected children is obtained from actual committed
  edges at the stable endpoint, so the inductive stability premise applies.
- Whole-tree recursion discharges all child Evidence. The independent successful
  Classify premise is retained; existence of a successful dictionary is not
  established.
- halted_dictionary_evidence assumes no step of the *full actual* relation,
  rather than no step of the restricted trace relation. Thus actual closure is
  applicable and is not weakened to subrelation maximality.
- Global policy in the generic theorem is stronger than root-only policy but
  explicitly stated. pending discharges it by defer=true. General B4, arbitrary
  refresh/reobserve, and executor membership in this trace remain open.

## View equality can be removed in a genuine fragment

GeneralDictionaryNominalOnlyRefresh175.lean proves five theorems using the
existing Refines relation on the fixed source carrier, but no equality of
normalized views. NominalOnly consists recursively of variable queries and
nominal queries whose children are NominalOnly. Finished nominal reports have
recorded descriptors at both interval endpoints. Refines preserves these
recorded descriptors exactly; variable leaves read no normalized view. This
suffices for inspect/inspectMany/report equality and same-model, same-key,
ordered-child-preserving Instance and Evidence transport.

This includes arbitrary finite depth and nonpoint nominal parameter intervals;
it excludes scalar and structural query nodes. It is a sufficient syntactic
fragment, not a new language acceptance restriction. Old input Evidence is an
explicit antecedent to transport, not an existence conclusion.

## Exact remaining reobserve gap

Actual `GeneralNominalReobservationSteps.Revision` retains the normalized view
but permits replacing the nominal descriptor entries. Its `Certified.raw` and
`Certified.exact` preserve model sets; they do not assert the syntactic report
or binding list is unchanged. `Improves` only asserts monotonic pointness and
one newly point-valued descriptor. Such revisions are not covered by
`Refines.nominals`, which preserves each old recorded descriptor under the
source embedding.

Therefore dropping the view-equality assumption does not solve general
reobservation. A smallest conservative extension is to derive the existing
finite `FootprintAt` condition for each historical packet from an independently
recorded descriptor-support invariant. This handles revisions away from the
packet's inspected footprint, but not revisions at a queried descriptor.

For queried descriptor changes, the missing producer must connect old and new
actual report bindings/materialization, including canonical child emission.
The current `Instance` definition fixes the exact ordered occurrence list.
Model equivalence by itself is not the required theorem of equality of that
syntactic list. A general repair likely needs correspondence of child demand
identities and current child Evidence under that correspondence, or a producer
of a compatible current packet. No such producer is assumed or silently
included in this review's theorem.
