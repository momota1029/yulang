# R26 admission and source intake

Sprint: ANNOTATION-HYGIENE-NATIVE-EVIDENCE/20261030-R26
Contract: `tasks/agent-loop/sprints/effect-permission-native-evidence-20261030-r26.md`, SHA-256 `8b2fcc72995472465b23fc397f257d07a035b0b1ba15f8f62ee31ae705dc11e5`.
Inputs: `tasks/agent-loop/sprints/effect-permission-native-evidence-20261030-r26-inputs.json`, SHA-256 `ec31c06563e6835101647272ce46930be55230481862621d8757b1193387e97d`.
Selector: `/root/next_action_selector`; fresh-envelope proposal after R25 closed incomplete.
Branch admission base: `fa2c3dcafbe412d4dd0c627b5f955f8e1429e83a`; isolated source base: `9a74a70a32ebda716a00c7203d8e606343cf442a`.

## R25/R24 disposition and live roster

R25 is CLOSED_INCOMPLETE under outcome SHA-256 `81ff25f3ee7d2d34f9facf7ea961c12e9630ea24b70934e235037d32ca3e6dab`. Its Rust source remains frozen and unreviewed. The R25/R24 time envelopes are not transferred. The R24 Lean candidate remains constructed but unchecked; its two earlier audit failures and the R24 Rust review findings remain frozen dependencies, not current proof/review results.

At `2026-10-29T19:36:01Z`, the live collaboration roster was synchronized: the primary was active and all returned child identities were completed; no child assignment was active. The R25 Rust author had confirmed STOP, and R25's reviewer had never been dispatched. A process snapshot found no active Cargo, rustc, Lean, or Lake command. Existing UNKNOWN worker rows and quarantined leases remain intact. No capacity override, path release, or unknown-writer cessation claim was used.

## Authenticated intake

Luna created detached worktree `isolated/ep-hygiene-r26/project` at `9a74a70a32ebda716a00c7203d8e606343cf442a`. Its working tree was clean. All eight Rust baseline pins inherited from R25 were independently matched against both the baseline Git blobs and the R26 worktree. The frozen R25 candidate hashes were rechecked: `machine.rs` `1d8ec9ac5ce4cb4a25e24dd81a2d15b901efd27107e047140676f27fd070ea40`, `receiving.rs` `dffb3fa5ce3d9437b347840e56fe5da80a143b358745f251838f66fa3065a23f`, `program.rs` `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907`. The R24 Lean candidate hash is `4bb9eafe2c0f7123c4d43722083190b9f7c78c2e0f6661160c5ccc56da1f7083`. R24/R25 source trees were not modified.

R26 output leases are exactly the ten paths in the contract/input manifest: six Rust paths and four Lean paths. Root UNKNOWN_WRITER runtime paths remain quarantined and untouched. The reviewer has no write lease.

## Envelope and ACK boundary

Fresh envelope: Rust 1,500 seconds; Lean 600; independent referee 1,000; Luna primary 3,600; Astra 0. Luna accounting starts `2026-10-29T19:36:01Z`, at 0/3,600 seconds. Child clocks remain at zero until current-session active-work receipts. The reviewer and both authors are WAITING for the pushed admission ACK. No Cargo, Rust compiler, Lean, Lake, formatter, or project test ran during admission.

Repository admission checks required for this sprint are `python3 tools/agent_sprint.py check` and `python3 -m unittest discover -s tools -p 'test_agent_sprint.py'`; they are static protocol tooling only. This admission checkpoint stages only `current.json`, this receipt, the R26 contract, and the R26 input manifest. The isolated worktree and unrelated dirty workspace paths are excluded.

The first static check correctly rejected changing `/root` from UNKNOWN: that identity is included in the existing capacity-release receipt. Its full worker row remains unchanged and UNKNOWN; the override and quarantined paths were not altered. The admission clock remains recorded in the sprint envelope.
