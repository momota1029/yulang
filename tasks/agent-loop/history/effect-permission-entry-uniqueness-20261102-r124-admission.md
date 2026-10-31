# R124 admission — Entry schedule uniqueness

Contract: `tasks/agent-loop/sprints/effect-permission-entry-uniqueness-20261102-r124.md`, SHA-256 `aca5c91ba535c9e2342bcd593bb6e8cffc062a506966f2777fcb818526fbc82e`.

Input manifest: `tasks/agent-loop/sprints/effect-permission-entry-uniqueness-20261102-r124-inputs-r1.json`, SHA-256 `2f7648717daf58a5132291d395a9eb84f7d78ad5305fc87068505ae31d68cf57`.

Baseline: branch `yulang3`, local and origin at `8914838a21ab2dcf62ccf14dddcec3ea91fd8446`. All eight immutable source/theory hashes and all three R123 evidence hashes were freshly authenticated. The dirty working copies are excluded.

## Roster and capacity

Immediately before admission, `collaboration.list_agents` showed `/root` running and all prior child agents completed, including the R123 producers, reviewer and selector. No RUNNING/WAITING child remains, so there is no pending notification or acknowledgement. Existing UNKNOWN worker observations and quarantined path leases are preserved. The existing capacity-only refresh remains effective for its exact prior 16 reservations; R124 releases no additional capacity and asserts no cessation for UNKNOWN workers.

## Exact assignments

- `/root/r124_entry_uniqueness_source`: researcher, 450 seconds, source handoff only at `tasks/agent-loop/inbox/effect-permission-entry-uniqueness-r124-source.md`.
- `/root/r124_entry_uniqueness_proof`: registered `lean_prover`, 300 seconds, proof handoff only at `tasks/agent-loop/inbox/effect-permission-entry-uniqueness-r124-proof.md`, after source freeze.
- Fresh independent compiler referee: 180 seconds after both handoffs freeze; read-only, no file lease.
- Luna primary closeout: 300 seconds; aggregate ≤1,230 seconds; Astra 0.

No source edits, build/test/compiler/Lean/checker execution, environment/storage probe, cache/worktree/copy or quarantined read is admitted. R111 and production gates remain open.
