# R178 — registration adequacy and pending-or-discharged consumers

Status: **revision 1 prospective-review candidate**. No semantic source read or
worker assignment starts until fresh exact-hash review is CLEAN and Luna
activates this contract.

Branch `research/simple-sub-intrusion`; activation HEAD
`e9a7a4fef3d6872fa0596646393a7c0473b3687b`; fresh cap 3000 seconds, no carryover.
Parent `notes/theory/2026-10-15-computation-forwarding-preservation.md`,
SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`.
Unchanged fixture `tools/inference-playground/examples/r171-formal-name-forwarding.yu`,
SHA-256 `cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f`.
R177 remains `CLOSED_UNFINISHED_RESEARCH`; its proof note and review do not
close any parent, A/B, source/native, implementation or production gate.
The frozen R177 Luna handoff is
`tasks/agent-loop/inbox/20261021-r177-implementation.md`, SHA-256
`ff5ccebad5bd4d18a3fef144a3e3c4256635147718b10be3275fb8183463b8ac`.

## Outcome and invariant

For the unchanged original source domain, analyze the construction-order chain
`source bound -> registration/qualification -> capture -> FreshUse admission ->
restoration/readback -> same-provider Apply -> both ordered Replay inputs ->
FunctionPort work -> execution or semantic discharge`. Establish source-bound
registration adequacy and a pending-or-discharged invariant through admission,
enqueue, processing, canonical delegation, reuse and rollback, or identify the
earliest precise missing constructor and owner. Couple the result to both
ordered Replay inputs and same-provider/use identity. A visitation or
generation marker alone is not semantic discharge. Preserve the parent's
quantifiers, shared xi, open incoming E, arbitrary finite chains/prefixes,
repeated/simultaneous entries, independent protections, pending/raw
continuations, alternatives, residual/scoped payloads, duplicate/canonical/
self-pairs, zero products, current/reused pairs and rollback cases. Apply each
valid lemma immediately to the original obligation; a conditional result leaves
it open. Resource erasure remains independently OPEN, including layout/capacity,
allocation and shared allocator effects, Arc identity/refcounts, rollback,
publication and unwind.

## Frozen inputs

Read only `/tmp/r178-inputs/baseline-7ec64a378/` and
`/tmp/r178-inputs/candidate-e9a7a4f/`, each eleven files mode `0444`, directory
mode `0555`. They retain R177's ten pairs byte-for-byte and add
`candidate_value_graph.rs`, whose registration owner was not inspected in R177.
SHA-256 by filename, baseline / candidate:

```text
candidate_call.rs       e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479 / same
candidate_context.rs    d884c20a98140da2a737d65f61faa97491bd9a2af7870bf3f0ea7dd428e9ffeb / a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733
candidate_effect.rs     c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1 / same
candidate_extrusion.rs  7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332 / same
candidate_intrusion.rs  475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97 / same
candidate_scheme.rs     9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225 / 48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25
candidate_source.rs     cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7 / same
candidate_value_graph.rs 19da9779e3e7866f5891e019e1cd343136ae0115bd1c47a02a7e7ee0cdfa80e0 / same
lib.rs                  c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985 / 24f480355979ee5d96305a08abf6aab67025ede32c2a1575b779e46f5e23b436
module.rs               153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907 / same
shadow_apply.rs         13ae8de60293b91e24659090649ff84002f5632a8909451d3f7bd8492b61bea5 / 2b0e46f28c328172477ac263360f4f3d01d27714dc62cd93235b8e3b1fe4e9ff
```

The proof packet contains the full pair manifest, parent/fixture and prior
receipt pins. The candidate source owner is the immutable R174-v6-plus snapshot,
not mutable checkout. Reviewer must verify all hashes/modes, output leases,
scope and allocation before any semantic source read.

## Lanes, leases and limits

After CLEAN, proof (Sol/high, 1380s) owns only
`notes/theory/2026-10-21-r178-registration-and-consumer-invariant.md` and
`tasks/agent-loop/inbox/20261021-r178-proof.md`. Luna/high (600s) owns only
`tasks/agent-loop/inbox/20261021-r178-implementation.md`, this contract's
sequential revisions and `tasks/agent-loop/current.json`. Luna analyzes
registration adequacy and actual provider/Apply identity on the pinned owners;
source status remains `NO_SAFE_CODE_SLICE`, with no edit authority. Proof and
Luna outputs remain disjoint. Changed source bytes require a new prospective
review. Children do not start a sprint team.

No compiler writes, tests/builds/probes, compiler/evaluator/Yulang2 execution,
network, nested CLI, Git, scratch output or semantic promotion. Parent, A/B,
source/native, implementation and production gates remain OPEN. Unknown and
legacy leases remain quarantined. Stop at outcome, blocker, budget, STOP or
session end and reconcile actual cessation.

| Work | Seconds |
|---|---:|
| Preparation and immutable manifests | 240 |
| Constructive proof | 1380 |
| Luna analysis | 600 |
| Prospective review | 120 |
| Final independent review | 300 |
| Conditional delta reserve | 120 |
| Closeout/state synchronization | 240 |
| **Total** | **3000** |

Preparation is charged 240s; 2760s remain reserved until CLEAN. Astra 0,
probes 0, no carryover. Unused reservations expire; UNKNOWN elapsed charges the
full grant. Final review covers source-to-consumer correspondence, source-bound
registration, both ordered Replay inputs, semantic discharge, resource premises,
parent application, exact pins and modes, leases, budget and preserved gates.
