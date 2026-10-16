# Sprint: pre-freeze one-shot snapshot observation boundary

ID: `npair-prefreeze-observation-boundary-20261017`.
Status: CANDIDATE until Luna freezes this contract and starts proof.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.
Primary and sole Git integrator: Luna.
Baseline: `d28b83ed498b6fb8d3959ca33c0d19c40f816f6e`.
Authority: adopted negative-pair definition and current NPAIR source/semantic boundary; post-solve API sprint is REVIEWED-PARTIAL only.

## Fixed outcome

Test one final discriminator before pursuing retained-output storage: determine
whether, inside `InferenceSession::run_candidate` after successful `execute()`
and before consuming `finish_observations`, an owner-bound read-only structural
observation can see live physical bounds without allowing mutation or an
unfinished route. Then produce a one-shot pre-freeze API contract or the exact
reason this owner point is unsafe/unavailable. If no safe point is established,
stop snapshot work; do not start another general audit.

Preserve all adopted semantics, original source occurrences and parent claims.
A pre-freeze observation can establish structural visibility only. It cannot
supply `eta_op`, `realization_op`, adopted `At`, source admission, N-Transport,
subtraction, receive consumption, production permission or parent closure.
Missing OwnerEmission/ExtrusionLink/FreshUse antecedents stay incomplete.

## Frozen direct inputs

Recheck all pins before reliance:

- `crates/yu-solver/src/lib.rs` — InferenceSession and finish boundary:
  `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`.
- `crates/yu-solver/src/candidate_intrusion.rs` — pending/dirty and mutation:
  `7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c`.
- `crates/yu-solver/src/candidate_context.rs` — physical/evidence lifecycle:
  `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6`.
- `crates/yu-solver/src/candidate_effect.rs` — processing/permissions:
  `11a1477ff2c35c03dccb70bdc6121d89d3ced9fadb1921cb8cf8cd5c093b07fb`.
- `crates/yu-solver/src/candidate_scheme.rs` — routes and captured graph:
  `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a`.
- `crates/yu-solver/src/shadow_apply.rs` — candidate solve path:
  `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`.
- Prior proof, SHA-256 `9e1ae6e71f095b89b09796e5da375d1f152427b658b6fe3bc045553632a4a3d6`.
- Prior reviewed-partial API proposal, SHA-256 `ee0cf9823b0cb7e44e512f535ec0dc4980df73fa69cf83aed0e0b4d4739f7488`.
- Prior outcome handoff, SHA-256 `59454380a265393359cc1e8c2340ed0e8b27a78055e4552ea4a991569b3bc79c`.

No source-owner expansion. Return to Luna if another pin is required.

## Proof lane — Sol/high first

Maximum 240 seconds. Write only:

- `notes/theory/2026-10-17-npair-prefreeze-observation-boundary.md`
- `tasks/agent-loop/inbox/20261017-npair-prefreeze-observation-boundary.md`

Inspect the exact live-session seam: `run_candidate` → successful `execute()`
→ `finish_candidate`/`finish_observations`. Establish/refute a borrow-scoped
observation point with all original bounds/effect_bounds still live. Trace
actual route journal, typed drain, replay/restoration and intrusion pending/
dirty completion conditions; `execute()` success alone is not a quiescence
theorem. Show same-owner enforcement from the actual owning `InferenceSession`,
not merely a common lifetime or matching IDs. Verify the callback/result cannot
escape past consuming finish. Preserve unavailable antecedents as incomplete.
Stop at the exact unsafe/missing premise or 240s; no code/execution.

## Implementation-readiness — Luna/high after proof STOP

Maximum 240 seconds. Write only:

- `notes/design/2026-10-17-npair-prefreeze-snapshot-contract.md`
- `tasks/agent-loop/inbox/20261017-npair-prefreeze-snapshot-contract.md`

Specify a private one-shot observation contract whose certificate/view is
consumed before `finish_observations` resumes. No borrow or physical vector
escapes into `FrozenInferenceData`; no retained-output storage, subscription or
code. Include checked live-slot resolution, owner identity, route/quiescence
gate, incomplete-evidence result, deterministic bounded enumeration and failure
disposition. If proof rejects the owner point, record that exact blocker and
WAIT; do not open another generic snapshot audit.

## Reviews, resources and stop

Authors are sequential: proof 240s then Luna readiness 240s. Fresh sequential
reviews after STOP: compiler_referee 60s, architect 60s, spec_auditor 60s.
Coordination 60s; total cap 720s, no reserve or carry-over. Astra 0. Preserve
three historical UNKNOWN reservations, board quarantine and foreign dirty
`authentic-source-and-forward-handler-20261017.json`.

No compiler source lease, tests/builds/probes/Cargo/source execution, source or
semantic changes, expected-output changes or production. If the live owner point
cannot be proved safe, stop snapshot work after this sprint. `eta_op` and
`realization_op` remain WAITING for original constructor evidence.
