# R113 closeout: unmatched expression request boundary

**Status: CLOSED_INPUT_BOUNDARY_PARTIAL_REVIEWED; fixed packet NOT_RUN.** The
rev3 pre-edit contract was CLEAN, but a producer source audit found a new
required input owner. Its contract says a new required owner stops the packet;
Luna kept that boundary and did not enlarge the pin set or retry.

The missing source bridge is `machine.rs::evaluate(Integer)` calling the
unpinned `runtime/literal.rs::integer(text)`. The retained HIR spelling `"99"`
and decoder call do not prove that the runtime request payload is native integer
99. Public preparation/admission of this exact source also remains unobserved
and open. The implementation worker created neither leased file. No test,
build, CLI, runtime, formatter or Git command ran. The one-shot R113 command
remains **NOT_RUN** and has no retry authority.

## Reviewed partial evidence

The proof author froze a conditional cursor/control argument and stopped at the
input boundary. A fresh independent compiler/source review returned CLEAN for
that limited claim: given the intended carriers and a reached unmatched request,
`ExpressionReturn(e, 1)` is moved unchanged through ordinary request
propagation into the saved continuation. The terminal outcome prevents normal
expression completion and the separate selected-`main` fallback from
executing or publishing 7. This is not a nonempty remaining `ExecutionRoot`
suffix, native payload=99 proof, public preparation result, complete CLI
prediction, resumption result, or parent-theorem closure.

- Contract rev3: [frozen R113 contract](/home/momota1029/rust/yulang/tasks/agent-loop/sprints/cli-outward-expression-suffix-20261019-r113-rev3.md), SHA-256 `f58944ee47053d6808c52fcc37a2fa97690f091a8d8f31942c433a1fe042559f`.
- Conditional proof: [cursor/control note](/home/momota1029/rust/yulang/notes/theory/2026-10-19-r113-module-request-suffix.md), SHA-256 `187d3372037cd8b27efef19e7e0ee238a27ed05bce82498e2c903a8853db9c2e`.
- Proof handoff: [R113 proof handoff](/home/momota1029/rust/yulang/tasks/agent-loop/inbox/20261019-r113-proof.md), SHA-256 `6737d27eb9b23973201d41d909a2f67fb67d35f52ca9b8cdf7c0d2a6d319f394`.
- Independent conditional source review: [R113 compiler review](/home/momota1029/rust/yulang/tasks/agent-loop/inbox/20261019-r113-compiler-review.md), SHA-256 recorded in current state.
- Rev1 and rev2 pre-reviews, and the CLEAN rev3 pre-review, remain preserved at their exact receipt paths. The rev3 spec auditor was read-only; Luna transcribed its verdict. The same transcription rule applies to the read-only compiler reviewer.

No production semantics changed. R113 closes as a failed fixed packet with
reviewed conditional evidence only. R111 remains NOT_RUN/FROZEN_UNVERIFIED and
untouched; R112 remains a finite source obstruction and R100-P2 remains OPEN.
All six effect-hygiene fronts, method/role behavior, ordinary/effectful runnable
source, A/B and adoption gates remain active parts of the user's broader goal.

## Next frontier

At the boundary selector, the recommended next target is wrong/sibling
permission, after pinning the exact authoritative proposition and an existing
source witness. Keep operation-name matching distinct from execution-owner
permission. The proof and implementation must share one already admitted
witness, trace its actual static/runtime consumers, and reach a public execution
entry. If no exact authority and fixture can be pinned, choose a different
under-covered front without expanding R113.
