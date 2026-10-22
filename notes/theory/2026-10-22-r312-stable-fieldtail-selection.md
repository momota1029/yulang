# R312 — stable FieldTail selection and same-use Member graph

Status: ACTIVE, solo primary, unreviewed. R149 remains OPEN.
Baseline: `3eb3b64eb`.
Contract: `tasks/agent-loop/sprints/r312-stable-fieldtail-selection-20261022.md`.

## Governing documents reread

Re-read the converted unified design §§4.1–4.5, 6, 9 stages 2/4 and 10, and the proof companion §§3.2–3.8, 4.5 and 7.2–7.4. The implementation must retain source occurrence and semantic payload together; method selection waits for the relevant receiver evidence and its stability condition. The Capture/FreshUse results transport records already in the graph and do not prove candidate completeness, source generation, selection soundness or source/native correspondence.

The effect correction remains binding: contravariant `[io]` means `[io,'e]`, so passing `[state]` alone is not a violation. Actual effect contributions remain present.

## Current source and solver evidence

R310 records an exact `SourceFieldTailObligation` with owner, occurrence, source key, member spelling, authenticated role-member candidate identities, receiver Value/effect rows and result Value/effect rows. Member templates are captured in a separate map keyed by exact `SourceMemberRootId`; no fake definition owner is introduced. Nested member-body FieldTail obligations remain in the Member graph.

The existing `FreshUse` already computes the four FieldTail row indices from the captured graph and retains that ordinal/index tuple with the same `rows` map. Its focused test confirms each local row is fresh and each shared anchor remains fixed. This is transport infrastructure, not a method selection.

The unresolved seam is selection: there is no consumer that proves the receiver's relevant bounds are complete and stable, matches them against authenticated role implementation sources, requires a unique applicable source, and then attaches one per-use FreshUse copy of the selected Member graph. `unique_role_member_schedule` only identifies one exact role-default schedule; it neither selects a receiver implementation nor certifies applicability.

## Next evidence

Trace the authentic `pair.say` obligation through `execute_candidate_graph_plan`, bound restoration and source implementation ownership. Identify the actual point at which receiver evidence reaches a fixed frontier and whether the existing solver state exposes a completeness witness. If so, connect only that witness to exact implementation identity and a unique member graph; if not, record the precise missing producer/consumer premise and leave the obligation pending. Test negative cases for stale or duplicate implementation identity, a later receiver-bound change, and independent uses.

No change to pinned Yulang2 bytes or effect semantics is authorized. Console remains independently blocked on the authenticated operator-use-to-value-owner candidate/runtime route introduced by R311. Neither sample execution nor any A/B, principality, termination, review or production gate is closed here.
