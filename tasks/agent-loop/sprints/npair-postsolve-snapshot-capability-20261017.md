# Sprint: post-solve snapshot capability and checked physical-slot resolver

ID: `npair-postsolve-snapshot-capability-20261017`.
Status: CANDIDATE until Luna freezes this contract and starts proof.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.
Primary and sole Git integrator: Luna.
Baseline: `ac838c252a6567cd92c186ebf928348565e8004e`.
Authority: adopted negative-pair definition and current NPAIR source/semantic boundary; prior owner-interface sprint revision 2 is REVIEWED-PARTIAL only.

## Original outcome and success evidence

Narrow the unresolved one-shot structural-validator prerequisite to a result that
has already successfully returned. Establish or refute whether that retained
post-solve result has an enforceable quiescent capability, same-owner identity,
and read-only access to the live physical bound slot. Then produce an exact
unapplied owner-local API contract for those properties, or name the precise
remaining blocker. Apply all findings to the parent without changing its claims,
quantifiers, original source occurrences or adopted semantics.

Success is a reviewed capability/resolver contract grounded in the post-solve
result owner and exact mutation paths, or an exact reviewed blocker that makes
implementation wait. The design must explicitly retain unavailable antecedents
as unavailable; accessors cannot synthesize them. This remains structural
readiness only. No `eta_op`, `realization_op`, adopted `At`, source admission,
subtraction, N-Transport, receive consumer or production claim follows.

## Frozen pins and owners

- `crates/yu-solver/src/lib.rs` — InferenceSession/CandidateSolvedResult:
  `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`.
- `crates/yu-solver/src/candidate_intrusion.rs` — transitive mutation owner:
  `7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c`.
- `crates/yu-solver/src/candidate_context.rs` — evidence/physical slot:
  `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6`.
- `crates/yu-solver/src/candidate_effect.rs` — formal permissions:
  `11a1477ff2c35c03dccb70bdc6121d89d3ced9fadb1921cb8cf8cd5c093b07fb`.
- `crates/yu-solver/src/candidate_scheme.rs` — GraphState/route:
  `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a`.
- `crates/yu-solver/src/shadow_apply.rs` — retained candidate result wrapper:
  `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`.
- Prior reviewed-partial readiness: `notes/design/2026-10-17-npair-snapshot-owner-interface.md`, SHA-256 `92c8934820604f895958bf8b2af773128def4c0007f4fb1ec0146eb416eb55f8`.
- Prior conditional proof: `notes/theory/2026-10-17-npair-snapshot-borrow-enumeration.md`, SHA-256 `5c008735438e191d52c4255d6d4b91b5eb2f810deb661a85c27b0061d29e1cb7`.
- Prior outcome handoff: `tasks/agent-loop/inbox/20261017-npair-snapshot-owner-interface.md`, SHA-256 `c4f15c09cb08facaf5ac836551dfb49d984c24c8abca60614fc2bd55816f79c2`.

Any transitive source read beyond these exact owners requires a new Luna boundary decision. Recheck all pins before reliance.

## Proof lane — Sol/high first

Maximum 300 seconds, up to five substantive stages. Write only:

- `notes/theory/2026-10-17-npair-postsolve-snapshot-capability.md`
- `tasks/agent-loop/inbox/20261017-npair-postsolve-snapshot-capability.md`

Inspect only a successfully returned candidate result. Determine whether
`CandidateSolvedResult`/the candidate wrapper is immutable after solve; trace
actual relevant mutation paths, including `candidate_intrusion`; distinguish
ordinary exclusive mutation from interior mutation; establish or refute
post-solve quiescence; show how a same-owner handle can be enforced across
simultaneously live results; and state whether a read-only resolver can check
the current physical slot by row-kind, lane, index and operand. Keep unavailable
OwnerEmission/ExtrusionLink/FreshUse antecedents explicit. No new source meaning.
If an exact premise fails, freeze that blocker and stop. No code or execution.

## Implementation-readiness lane — Luna/high after proof STOP

Maximum 300 seconds. Read the frozen proof output and write only:

- `notes/design/2026-10-17-npair-postsolve-snapshot-api-contract.md`
- `tasks/agent-loop/inbox/20261017-npair-postsolve-snapshot-api-contract.md`

Produce an exact unapplied API/patch proposal (no code) for owner-bound snapshot
construction, complete enumeration of retained records, checked live physical
slot resolution, explicit incomplete-evidence results, and shared traversal
with repeated-scan/work/temporary-storage accounting. State which proof
premises the proposal consumes and which remain unproved. No compiler source
lease or executable validator follows automatically.

## Reviews, resources and stop conditions

Sequential authors: proof 300s, then readiness 300s. Fresh reviews after both
STOP: compiler_referee 120s, architect 60s, spec_auditor 60s. Coordination 60s,
reserve 60s; total cap 960s. Astra 0. No automatic extension or carry-over from
the closed sprint. Preserve three historical UNKNOWN reservations, board
quarantine and foreign dirty `authentic-source-and-forward-handler-20261017.json`.

No tests/builds/probes/Cargo/source execution, code changes, expected-output
changes, source admission, semantic changes or production. A post-solve
capability result alone cannot establish successful source construction or the
parent theorem. STOP at an exact blocker or cap; implementation remains WAITING
if quiescence, owner identity, physical-slot resolution or evidence completeness
is unproved.
