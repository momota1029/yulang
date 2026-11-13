# Next nonterminal fragment: request identity before semantic renaming

Read-only analysis, NOT a newly proved theorem. Existing source inspected:
`GeneralNominalMaterialization.inputRequests/emissionRequests/requests`,
`GeneralCanonicalChildOrder.canonicalEmit`,
`GeneralNominalAllocation.source/source_preserved/source_identity`.

For the current Revision, seed, invocation/root identity, declaration and allocation
keys stay fixed. The nonterminal request list may be invariant even when emitted
child demand intervals are not. `inputRequests` drops normalized `.var` patterns;
these are precisely the inputs whose endpoints come directly from captures.
Non-variable input requests use allocated endpoints. Associated-output targets use
capture.outputs/allocation.outputs, unchanged in this Shape. Thus first prove an
emissionRequests invariance lemma, then lift over canonicalEmit. Do not start by
inventing an arbitrary retargeting relation.

Narrow next proof target: one requirement with normalized variable input arguments,
checked parent, singleton binder, existing depth-two Shape/query agreement,
old parent BranchModels and current source Models in the same assignment.
Then emitted input requests vanish, leaving root/output actual-mode requests.
Use ActualSchema.generated_actual, derive origin coverage from before_exact and
after_exact, and derive Fits inclusion with NonpointCollapse.capture_fits.
For the request-identity part use rename=id; semantic root equivalence is reflexive.
Prove generated-use scope or explicitly isolate unchanged captures for other names.

This can transport the PARENT branch, not recursively validate the child Evidence.
Child demand intervals change, while purpose-6 child identity remains fixed.
Actual current child Evidence needs its own semantic transport argument. Historical
Evidence for all current journal models remains a separate missing invariant.

Compound input patterns emit lower/upper requests. Our actual-only replay does not
apply automatically: structural paths preserve the incoming mode. Nominal schema
nodes reset nested variables to actual mode, so a future structural induction may
separate nominal-covered variables from genuinely lower/upper variables. No such
classification is proved here; the cycle160 lower-mode counterexample prevents
unqualified Fits-only widening.

For truly changed seed/invocation identities, freshness and injectivity prove no
source-type equivalence. The explicit semantic equations required by
ActualSchemaOrigin.replay must come from actual allocation/propagation semantics.
