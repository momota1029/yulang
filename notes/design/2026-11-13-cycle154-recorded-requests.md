# Recorded variable-free materialization requests

Status: conditional soundness extension.

Target the fresh-target limitation of Observed. Every packet in an actual
reachable Value journal retains a full historical BranchModels obligation.
Its variable-free request-test subsets therefore hold for every final model without
an initial observation or a source-slot witness for the target.

First prove actual reachable-journal schema coherence: for every retained
packet and fixed request batch, current generation equals generation at the
packet context. Next restrict the historical packet's tests by request-list
membership, and eliminate all report/capture-specific obligations with the
explicit syntactic `variables = []` condition. Specialize to rootRequests,
whose inclusion in the actual packet request batch is unconditional.

This does not derive variable-freeness, final model existence, or
current head inspection. It proves materialization validity, not full Instance
or Evidence. Existing definitions and semantics are unchanged.

Validation: focused `lake build Yulang.GeneralDictionaryRecordedRequestModels
--wfail` passed (710 jobs), and direct trust-zero audit checks six public
results plus SchemaCoherent using only standard axioms. The private list-test
expansion lemma is a dependency of subset_tests. No full build was run.

## Actual readiness provenance

The installation rule contains Prepared and the actual argument lookup. Their
common bounds recover RequestReady and its unknown=false field. Retained packet
membership transports this fact through all later reobservation steps, without a
model-existence premise. The subset law then proves every recorded sub-batch has
unknown=false at the current context. reachable_root_closed combines this derived
knownness with the explicit variables=[] premise. The first variable-free Models
theorem alone deliberately makes no readiness claim.

Final module: 12 public theorems, two private list lemmas, two invariant definitions.
All public results and invariant definitions pass trust-zero audit; the focused
complete declaration dependency gate additionally covers private/generated terms.
