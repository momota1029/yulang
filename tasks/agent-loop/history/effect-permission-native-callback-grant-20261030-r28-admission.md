# R28 admission and live-state reconciliation

Sprint: EFFECT-PERMISSION-NATIVE-CALLBACK-GRANT/20261030-R28. Status: admitted by Luna; assignments are NOT_STARTED until fresh launch receipts arrive.

## Frozen admission inputs

- Baseline and upstream before this checkpoint: c9e315208cb04bcc4fe8c3595d929fb76538f1cd on yulang3/origin/yulang3.
- Contract: tasks/agent-loop/sprints/effect-permission-native-callback-grant-20261030-r28.md; SHA-256 fa1a6f2e450169748e0696fb607963147a46cc4e6c464087cdefcacec383d89a.
- Schema: tasks/agent-loop/sprints/effect-permission-native-callback-grant-20261030-r28-schema-r1.json; SHA-256 fb46c1c031ee9132385c2170c22cbf8ea5eb27a8dc176ce0ba6356b7cf4a71ea.
- Inputs: tasks/agent-loop/sprints/effect-permission-native-callback-grant-20261030-r28-inputs-r1.json; SHA-256 ca55123ef61014258f9d60d327cf0a3b0db069231bcdfa3563b812913ff901f1.
- R27 closeout: tasks/agent-loop/history/effect-permission-owner-certificate-20261030-r27-active.md; SHA-256 955dd030e12428435d055db5be15c4430017db63c17690049e273d1af9b0ced4. R27 is CLOSED_INCOMPLETE; no Rust, Lean, review or Luna reserve transfers.
- R26 accepted conditional Lean module: SHA-256 0621f43739c12ce1e7919a50de129414a4748d8359bf46740babd69f4854011e. It remains an abstract conditional result, not source/native closure.

## Dispatcher and bounded choice

At the R28 start boundary, next_action_selector recommended one packet that combines the exact R27 Rust owner-certificate repair/evidence with a native callback Grant bridge into the R26 conditional model. A separate read-only task decomposition identified native callback entry/Name/use/execution/Grant correspondence as the decisive hygiene premise and marked broad solver permission consumption blocked pending that invariant. The selector adjudicated the seam: prioritize the native callback bridge, use companion owner replay as supporting evidence, and keep broad solver writes outside this packet.

This preserves the original parent and user-selected [E] semantics. It adds no production authority, changes no solver/runtime decision, and does not promote the R27 or R26 result. R27's unchecked TemplateOwnerReplay artifact remains an unconsumed archival item and is not imported by this packet.

## Live roster, current-state compaction and custody

The live collaboration roster was synchronized before admission. Both R27 children, /root/effect_permission_owner_certificate_r27_rust and /root/effect_permission_owner_certificate_r27_proof, returned completed status; their closeout records no descendants or remaining processes. No R28 worker has launched. Existing completed review/decomposition children are not treated as active work. The interrupted R22 review remains historical and no path is reused from it.

The stale /root/latent_demand_transport_classification_r17_source row was absent from the live roster and remains WAITING in current.json. Its held inbox lease is unchanged. UNKNOWN workers and quarantined root runtime paths remain unchanged. The already authenticated 13-slot capacity override remains exactly as recorded; this admission neither reapplies it nor releases any path.

After confirming R27 worker cessation and archiving their exact pins above, Luna takes custody of R27's existing unconsumed frozen/held output paths. This is an ownership handoff only: source paths remain FROZEN, unconsumed module/cache/scratch outputs remain HELD, and no such path becomes available for writing. The two STOPPED R27 worker rows are removed from the compact current snapshot; their worker identities and cessation/output receipts remain in the R27 closeout.

The compact snapshot also drops only resolved lease reservations for the closed R27 contract, consumed Rust handoff/preflight records, the superseded R2/R3 rejected candidate archives, and the absent R27 proof handoff path. Their files remain in immutable Git history where present; no file is deleted. The closed R21 outcome lease remains because adjacent open Call work still refers to it. All UNKNOWN rows, quarantines, pending obligations and unconsumed R27 artifacts remain represented.

Root workspace contains pre-existing unrelated tracked modifications and untracked isolated work. They are excluded from R28 leases and staging. The quarantined root machine.rs/receiving.rs hashes and the primary-owned solver hashes remain untouched. W is a new detached worktree at the committed baseline; its source machine.rs/receiving.rs match the input manifest. The copied CallbackHygieneCorrespondence.lean overlay matches SHA-256 0621f43739c12ce1e7919a50de129414a4748d8359bf46740babd69f4854011e and is read-only.

## Assignments and resources

R28 Rust lane: /root/r28_rust, implementer, Luna/high, 1,150 seconds; exact output and handoff paths are in the contract/current.json.

R28 Lean lane: /root/r28_proof, registered lean_prover leaf, 1,000 seconds total. The initial construction slice is capped at 350 seconds; the worker must stop rather than wait for authenticated Rust records. Up to 650 seconds remain reserved for application/audits after a fresh resumption receipt.

Independent review: /root/r28_review, fresh compiler_referee, 1,200 seconds after both author outputs freeze. Luna primary allocation is 3,850 seconds including 500 seconds for closeout. Astra allocation is zero. Aggregate sprint envelope is 7,200 seconds; R27 time is not transferred. Heavy processes serialize; Cargo is capped at 360 seconds and Lean audits at two/120 seconds.

No compiler, test, Lean/Lake, formatter, runtime or solver command ran during admission. R28 assignments are prepared but not launched. The admission checkpoint must be pushed before child launch. Original source/native, whole-language hygiene, soundness, principality, termination and production gates remain OPEN.
