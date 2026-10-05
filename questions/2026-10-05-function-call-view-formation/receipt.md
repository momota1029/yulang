# Integration receipt: function-call-view-formation/q1

Question revision: `q1`
Approved answer: `function-call-view-formation-answer/a2`
Branch: `research/simple-sub-intrusion`
Integration commit: `61a3651376166346a5baa03ec6679c310b0edbdb`
Outcome: accepted user decision; detailed rules and implementation remain gated

## Validation

- The question, current draft and approved answer identify the same question
  and answer revisions. The approved answer embeds the complete current `a2`
  draft byte-for-byte.
- `approved-answer.md` records the user's approval and the original statements
  selecting option 2 and clarifying `f`'s protected Handler treatment and the
  annotation-dependent `io` allowance. The answerer's interpretations are
  explicitly distinguished and included in the approved scope.
- The source revision named by the question, `d90ba4425038cf86ff932ed42eb309931e143fd8`,
  is an ancestor of the integration commit. The four named governing design
  sources match their blobs at that revision. The current question, draft and
  approved answer match their committed versions.
- Only `question.md`, `answer-draft.md` (`a2`) and `approved-answer.md` were
  integrated. The `a1` archive remains excluded.

## Integrated decision and affected scope

Option 2 is selected: form complete role-indexed callback contracts and their
source identities, profiles, typed paths, owner/receiver incidences and
correlated original constraints from relevant declarations, uses and recursive
components. Admission remains independent of the pending Function comparison.
For unannotated `f`, the approved direction treats its inferred effect as
fully handler-protected; ordinary-value evidence can determine during
inference that the callable is not a Handler. Annotation presence controls
protection: the specified `[io]` annotation permits removing `io` from `f`,
without asserting that removal occurs or authorizing removal of unrelated
effects. Callback-literal B, actual roles of supplied values, existing
annotation and Function decisions, production Option 2 and Option A remain in
force.

The direction is recorded in
[`inferred Function call views`](../../notes/design/2026-10-05-inferred-function-call-views.md),
which now has Authoritative status after pre-write scope and closure
conformance reviews found no issues. That review closes documentary
conformance only. The answer selects no completed inference rules,
uniqueness/principality proofs, solver algorithm, production membership or
compiler implementation. Affected gates remain callback source adequacy,
complete Function formation/admission, production conformance and inference
replacement. No theory or implementation gate is closed by this receipt.
