# Cycle161 module guide

V5 stays 8/14 open. These are semantic transport helpers and concrete regressions,
not completeness/principal-typing or unrestricted progress theorems. Full quantified
types and file hashes are in notes/verification/dots-cycle-161-signatures.txt and inventory.json.
EmissionRequestIdentity (3 theorems) is inherited from cycle160, not new this cycle.

|Module (GeneralDictionary prefix omitted)|Public theorems|
|---|---:|
|ChildCaptureExample|11|
|ChildCaptureTransport|8|
|EmissionRequestIdentity|3|
|NonterminalCertifiedEvidence|23|
|NonterminalChildEvidence|13|
|NonterminalNamedEvidence|2|
|NonterminalNamedExample|16|
|NonterminalNonpointBranch|2|
|NonterminalNonpointEvidence|2|
|NonterminalNonpointExample|15|
|NonterminalOldObstruction|7|
|NonterminalRecordedRevision|2|
|NonterminalScope|7|
|RecordedLeafPlans|1|
|RequestSnapshot|5|
|ValuePendingExclusion|4|
|VariableIntervalLeaf|3|
|VariableLeafPlans|5|
|VariableWhereRequests|6|

## Quantified claims and retained premises

- RequestSnapshot: arbitrary registry/declaration/root and capture bounds, under fixed
  allocation plus actual Revision preserving seed/output capture, whole ordered
  materialization request list/generated schema/readiness equal. Child demand intervals
  and semantic Evidence are not equalities inferred from this.
- VariableWhereRequests: actual emitter/canonical request facts for normalized variable
  where inputs, with or without named outputs; bare fragment has no child output request.
- NonterminalNonpointBranch: any existing depth-two collapse Shape, singleton binder,
  query equality, variable-normalizing child inputs; old BranchModels and current source
  Models in the same model imply current parent BranchModels, without leaf endpoint
  equivalence. Generated name scope must be supplied or derived in bare fragment.
- NonterminalScope: Checked declaration scope plus normalized RHS syntactic scope yields
  generated variable scope. Normal-form or normalized-variable RHSs discharge it. This is
  not a proof of general normalize-vars-subset for all record/variant patterns.
- NonterminalNonpointEvidence / NonterminalNamedEvidence: checked registry key uniqueness,
  visible declaration, actual old Instance/Evidence, same-model source Models, actual
  root arguments, singleton binder and Shape imply current Instance. Evidence also needs
  independent current children Evidence; old children are not reused by false equality.
  Named adapter permits child outputs under syntactic normalized output scope.
- NonterminalRecordedRevision: a restricted report-preserving historical trace supplies
  old Instance from its proved invariant; a Certified final Shape revision supplies old
  model via exactness backwards. No arbitrary-history invariant, enabled final Step,
  child Evidence, or selection theorem is smuggled in.
- ChildCaptureTransport: arbitrary same-seed capture replacements preserve the complete
  child identity list/order/multiplicity and output allocation; normalized variable
  child Fits follows captured Fits. Existing Shape gives Fits inclusion, not equality.
- VariableIntervalLeaf: terminal bare-variable declaration accepts a located source
  interval in a source model when its endpoints are ordered; neither equal endpoints nor
  point intervals required. Root output demand is empty in this leaf helper.
- NonterminalNonpointExample / NamedExample: concrete checked parent, nonempty child,
  nonempty associated schema and nonpoint leaves. Named fixture additionally has actual
  child named output and two generated variable uses. BranchModels only, not execution.
- ChildCaptureExample: genuine same child identity with strictly different emitted
  demands and strictly enlarged Fits. Not a counterexample to Certified soundness.
- NonterminalChildEvidence: builds actual canonical current child Instance/Evidence and
  full parent node31[node32[]], rather than assuming recursive evidence.
- NonterminalCertifiedEvidence: same checked two-declaration registry and same outputRoot
  throughout an actual improving Certified reobserve Value Step, reachable/formed state,
  current Models and full current source Evidence. Certificate comes from universally
  interpreted initial ordinary equalities. The current model has bottom/int child
  endpoints and one root associated variable use. No selected dictionary, installed
  output, Stable result, or arbitrary reachable-state theorem.

## Next boundary

The positive certified witness and restricted-trace transport shrink different gaps.
A general bridge still must obtain current recursive child Evidence for arbitrary
recorded candidates and revisions, prove parent scope beyond the syntactic fragment,
and establish root/selection/output-installation invariants. None is a language
rejection rule. Named child-output positive BranchModels does not yet entail child
Evidence with a named-output installation. Keep these obligations distinct.


## Old recursive Evidence obstruction (7 new public theorems)

`NonterminalOldObstruction.root_no_evidence` quantifies over every assignment and
payload for the unchanged checked certified fixture: the actual old child uses private
merged IDs not located in the old source, so recursive source Evidence does not exist.
The actual revised context has full current Evidence. This is availability after revision,
not preservation of an old full dictionary; the conditional adapters retain non-vacuous
use only when callers really supply or derive old source Evidence. Candidate-private
BranchModels and recursive located Evidence must never be conflated.

## I-26 update received during cycle

Fresh integration62cba43b5 adds the unsettled-output delay rule in spec6.3 and inboxI26.
The exact supervisor document changes were merged; no new operational guard definition
was supplied in that commit. Semantic Evidence is not runtime selected classification.
The new rule must be connected to Astra's forthcoming guard/Step/Stable, without deleting
ordinary equalities or changing the independent Evidence judgment. See the I26 boundary
review note. No claim of implementing the new delay guard is made.


## Existing Value support-pending exclusions (4 new public theorems)

`ValuePendingExclusion` derives no selected local frontier, no selected B4 local
frontier, no selected Classify dictionary, and no completed parent dictionary when
one child of its selected local child list is SupportPending. Quantification is over
arbitrary registries/tracked states/roots/payload dictionaries. The negative facts
need no root-ready/no-K2 premise; positive pending classification still retains K2
priority. This is the older Value guard, not I26's forthcoming new predicate, and
it does not negate independent semantic Evidence. Two private eliminators are also
covered by the all-declaration dependency gate.


## Finite leaf plans and restricted recorded trace (6 new public theorems)

`VariableLeafPlans.LeafPlan` supplies a visible checked declaration, exact key/role,
variable query/input binder, terminal requirements, empty child named-output demand,
actual located interval and endpoint order in the specified model. It does NOT contain
Instance or Evidence. Source Models and Metadata derive each leaf Instance/Evidence,
then ordered/multiplicity-preserving All₂ child Evidence and parent Evidence. The fifth
theorem transports an actual old parent Instance and uses plans for exactly the newly
computed canonical child list.

`RecordedLeafPlans.evidence_from_leaf_plans` combines the restricted historical trace
invariant and Certified final depth-two collapse with plans for all actual current
children. Historical parent Instance and current Metadata are derived, not assumed.
No old parent Evidence/current child Evidence premise is used. This is an explicit
finite terminal-variable leaf fragment. It is not a construction of such plans from
arbitrary guarded selected children or a general executable tree bridge.
