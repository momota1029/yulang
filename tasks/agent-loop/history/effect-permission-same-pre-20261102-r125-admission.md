# R125 admission — same Rust PRE-state to R39

Contract: `tasks/agent-loop/sprints/effect-permission-same-pre-20261102-r125.md`, SHA-256 `e064495d96385942c79cfacdec5ce7be6b060db7be4f820c79a1096fcc9862cb`.

Input manifest: `tasks/agent-loop/sprints/effect-permission-same-pre-20261102-r125-inputs-r1.json`, SHA-256 `fcb027ef75256c3a0d7f5318af669767334818f7f217d8948f9bfb3b83252efa`.

Baseline branch `yulang3`, local and origin at `bf83716eea816536f3cc1d68b323d1567712dd38`. All eleven immutable source/theory hashes and eleven prior-evidence hashes were freshly authenticated. Dirty working copies are excluded.

## Roster and capacity

Immediately before admission, `collaboration.list_agents` showed `/root` running and all child agents completed, including R124 producers, reviewer and selector. No RUNNING/WAITING child remains, so no notification or acknowledgement is pending. Existing UNKNOWN observations and quarantined path leases remain unchanged. The capacity-only receipt remains effective for exactly its prior 16 reservation identities; R125 releases no further capacity and asserts no cessation for UNKNOWN workers.

## Exact assignments

- `/root/r125_same_pre_source`: researcher, 450 seconds, source handoff only at `tasks/agent-loop/inbox/effect-permission-same-pre-r125-source.md`.
- `/root/r125_same_pre_proof`: registered `lean_prover`, 300 seconds, proof handoff only at `tasks/agent-loop/inbox/effect-permission-same-pre-r125-proof.md`, after source freeze.
- Fresh independent compiler referee: 180 seconds after both outputs freeze; read-only, no file lease.
- Luna primary closeout: 300 seconds; aggregate ≤1,230 seconds; Astra 0.

No source edits, tests/build/compiler/Lean/checker execution, storage/environment probes, copies/worktrees/caches or dirty/quarantined source reads are admitted. R111 and production gates remain open.
