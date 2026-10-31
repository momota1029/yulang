# R123 admission — computation-entry lifecycle

Contract: `tasks/agent-loop/sprints/effect-permission-entry-lifecycle-20261102-r123.md`, SHA-256 `d715f6f26267c7ab14f2451ede516ddba8184b91f899ebf5005f9b5477104623`.

Input manifest: `tasks/agent-loop/sprints/effect-permission-entry-lifecycle-20261102-r123-inputs-r1.json`, SHA-256 `47adc3f89a2426f46cffdecfed8fa74bfdb0fac42f4deb4722fc94d70f6578aa`.

Baseline: branch `yulang3`, local and `origin/yulang3` at `852ab889cee2f4cfe04da3a1e8c9dd96f9758845`. All inputs are immutable commit/blob pins; working-tree solver edits and quarantined runtime files are excluded.

## Roster and capacity

Immediately before admission, `collaboration.list_agents` showed `/root` running and every prior child completed, including all R122 producers, reviewer and selector. No prior child is RUNNING/WAITING; there are no notifications or acknowledgements pending. Current UNKNOWN worker observations and quarantined path leases remain unchanged. The existing capacity-only receipt `tasks/agent-loop/history/20261102-capacity-release-refresh.md` remains effective for exactly the previously authorized 16 reservation identities; this admission releases no additional capacity and asserts no cessation for UNKNOWN workers.

## Exact R123 assignments

- `/root/r123_entry_lifecycle_source`: researcher, 400 seconds, source handoff only at `tasks/agent-loop/inbox/effect-permission-entry-lifecycle-r123-source.md`.
- `/root/r123_entry_lifecycle_proof`: registered `lean_prover`, 300 seconds, proof handoff only at `tasks/agent-loop/inbox/effect-permission-entry-lifecycle-r123-proof.md`, after source freeze.
- Fresh independent compiler referee: 180 seconds only after both outputs freeze; read-only, no file lease.
- Luna primary closeout: 300 seconds. Aggregate ≤1,180 seconds; Astra 0.

No source edit, build/test/checker/execution, Lean process, environment/storage probe or quarantined read is admitted. R111 and all production/parent gates remain open.
