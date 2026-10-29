# R26 Rust author handoff — R2

Status: **frozen for fresh exact-hash review; no compile or runtime authorization**.

## Assignment and resource receipt

- Worker: `/root/effect_permission_hygiene_r24_rust`.
- R2 active start: `2026-10-29 20:12:59 UTC`; freeze: `2026-10-29 20:18:10 UTC`; active interval: 311 seconds of the 400-second R2 cap. The 20:17:46 UTC progress update preceded actual freeze by 24 seconds.
- Requested model/effort: Luna/high; observed: UNKNOWN. Descendants/processes: 0. No Cargo, compiler, tests, formatter, Lean/Lake/checker, or Git commands were run.
- Exact write leases: R26 `machine.rs`, `receiving.rs`, `program.rs`, `receipts/hygiene.json`, `build-target`, and this handoff only. `build-target` is absent in the isolated tree and was not created.

## Frozen candidate hashes

| Leased artifact | SHA-256 |
| --- | --- |
| `isolated/ep-hygiene-r26/project/tools/inference-playground/src/runtime/machine.rs` | `c232c15d5260f68e50bf45493a15f99ce053267c895e8a382e1065963d3b3a3c` |
| `isolated/ep-hygiene-r26/project/tools/inference-playground/src/runtime/receiving.rs` | `dffb3fa5ce3d9437b347840e56fe5da80a143b358745f251838f66fa3065a23f` |
| `isolated/ep-hygiene-r26/project/tools/inference-playground/src/runtime/program.rs` | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` |
| `isolated/ep-hygiene-r26/project/receipts/hygiene.json` | `2b8be967abbd33eb45846b3a26c4616bf58b7d60539499962f53b19a0c369577` |

R2 uses schema canonical SHA-256 `118319c84980812e0a2bf5f5f4c968ddd4fba2fd08cdac0a65ca841510c0f9e7`. R1 archive remains immutable. Only `machine.rs`, the hygiene receipt and this handoff changed in R2; both routes, their sources, and outputs remain unchanged. The handoff's own raw SHA-256 is reported in the stop receipt.

## R2 observation and validator repair

- Added test-only `TemplateOwnerResolution` at the `TemplateNode::Owner` branch, capturing exact template/node, original owner, control-resolved owner, previous owner, selected owner, borrowed/fresh disposition, and the existing owner-open call/provider identity on fresh selection. Owner selection and control resolution remain unchanged.
- Added `ContinuationCapture.outer_control_chain`, separately snapshotting actual retained `CatchReturn`, `OwnerReturn`, and `ReceiverReturn` frames with stack indices/order and source/owner identities. The inner saved-suffix evidence is unchanged and does not include these frames.
- Reworked the companion validator to join `ContinuationApply` to its actual `OwnerOpen`, replay the observed control-map/previous-owner chain through owner-resolution events, and join the retained write request to its selected owner. The outer write Catch must match the exact captured handler occurrence, owner, site, and ordered surrounding boundaries. The response value and view remain separate joins to the same write request.
- Removed the invalid equalities between application owner, retained request owner, signal Catch owner, and inner suffix owners.
- Added rejection mutations for missing/substituted owner-resolution identity/disposition; missing/substituted outer handler, receiver/owner boundary, and reordered chain; disconnected retained write event. Earlier callback/companion mutation families and asserted results `1` and `23` are retained.

## Evidence limits

No Rust compiler or runtime test was executed. The two route result assertions remain unexecuted assertions, not runtime observations. This author handoff is not independent certification. The next authorized step is fresh independent exact-hash source review; compile remains unauthorized until a separate exact-hash ACCEPT. Runtime tests require a later distinct ACCEPT. Any source edit invalidates this review target.

The candidate is test-only evidence. It does not prove owner transitions from an executed trace, native grant/RootComp reachability, whole-language effect hygiene, original A/B closure, soundness, principality, or production readiness. Luna owns cleanup or any subsequent repair lease.
