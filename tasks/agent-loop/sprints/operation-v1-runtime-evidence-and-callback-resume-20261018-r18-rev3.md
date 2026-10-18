# r18 revision 3 — distinguish continuation return from callback invocation

This amendment retains every r18 revision 1 and revision 2 claim, quantifier, source domain, success condition, semantic constraint, production boundary and parent scope. It responds to the fresh independent review blocker: `continuation_apply` is the inner `k response` Apply, while the callback invocation is the distinct surrounding Apply that consumes the catch result.

## Fixed repair outcome

Keep the three source applications distinct and evidence-linked:

1. `continuation_apply`: the handler-arm `k response` application that selects and enters the saved continuation.
2. `response_invocation_apply`: the unique surrounding source Apply that receives the catch result and invokes the exact returned response closure after the raw continuation returns, while the outer catch remains active.
3. `callback_apply`: the Apply inside the response closure body that issues `outer::next` (or the chosen outer operation).

Derive `response_invocation_apply` uniquely from the same retained HIR/runtime code structure and exact response definition/catch result path. At runtime, record its application as evidence only if its callee is the exact closure handle returned through the `ResumeArgument`, and the executable closure retains the same captured environment. Keep `continuation_apply` to authenticate `k response`; do not remove source-site checks, infer a join from equal closure type/family, or accept an arbitrary call of the same closure. The callback operation event must still arise from the closure body at `callback_apply`, with the exact declaration and same invocation lineage, reach the actually live outer handler, select and evaluate its arm, and finish as `Completed(Integer("42"))` before publishing the joined receipt.

The existing `local_grant`, exact same-HIR successful FieldBoundV1 receipt, both bounded function-response gates, explicit research-only entry, runtime failure/mismatch/unhandled/exhaustion/wrong-result rejection, ordinary and scoped defaults, source fixture and rev2 order remain unchanged. Add/retain a negative control showing that invoking the same closure at a different Apply site cannot publish a completed receipt.

No claim says the callback Apply is inside the raw saved suffix. The parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN; original conditions closed remain 0. This amendment grants no production authority and does not close soundness, principality, termination, general source coverage, F1/FK1 or N-Transport.

## Exact continuation lease

Luna grants the implementation owner one bounded repair packet on:

- `tools/inference-playground/src/runtime/program.rs`
- `tools/inference-playground/src/runtime/machine.rs`
- `tools/inference-playground/tests/runtime_resume.rs`
- `tasks/agent-loop/inbox/20261018-operation-v1-runtime-resume-implementation-r2.md`

`tools/inference-playground/src/lib.rs` and `src/runtime/continuation.rs` remain frozen/read-only dependencies. Solver files and proof artifacts remain frozen. The previous r18 implementation/handoff stays immutable as the reviewed r1 snapshot. No source-form rewrite, semantic rule change, lease expansion, formatter-wide rewrite, or production route is authorized.

Freeze exact hashes and stop before checks. The same independent compiler reviewer assigned by Luna reviews the exact delta against this amendment, with special attention to distinct Apply identities, same-handle/environment dataflow, mismatch controls, preserved `local_grant`, and receipt suppression. Only after CLEAN may Luna run the focused `yu-playground` `runtime_resume` target. If the test exposes an acceptance or grant boundary, record the exact first boundary and return through Luna; do not weaken the source's Written field or success predicate.

## Resource amendment

The original 3000-second envelope stays fully charged; no unused time is restored. This versioned continuation adds 900 seconds, for a total cap of 3900 seconds and 3900 conservatively charged when issued: implementation repair 360 seconds, independent delta review 240 seconds, focused runtime execution/integration/state 300 seconds. Astra allocation remains 0. No automatic renewal or carryover.

## Stop conditions

Stop at the first of: frozen repair handoff, 360-second implementation reservation consumed, reviewer BLOCKING, focused test boundary, or total 3900 seconds charged. Do not publish a runtime completion claim before the focused test returns a same-HIR success receipt. Preserve the independent-review result and r1 snapshot. Parent closure is 0 unless an original parent condition is separately proved with its required review.
