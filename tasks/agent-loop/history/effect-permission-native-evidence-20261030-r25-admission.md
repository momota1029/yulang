# R25 admission and source intake

Sprint: ANNOTATION-HYGIENE-NATIVE-EVIDENCE/20261030-R25
Contract: tasks/agent-loop/sprints/effect-permission-native-evidence-20261030-r25.md, SHA-256 6bcc5d6bb5b2482564af254a6efdd7da1d3c95f162c91f9ba0d58d6e3861d3ba.
Inputs: tasks/agent-loop/sprints/effect-permission-native-evidence-20261030-r25-inputs.json, SHA-256 ba35b35d6ebbe8a6925827fb3bca1f645acbe62a661ed95e8cde50998508cb05.
Prior R24 outcome: SHA-256 d2dd2d91d9bed9efb8f85e05997dfe4f7053512061f72dd6cd377fef3dd08b74.
Admission base: 32f93ca422f2986b85b235864f6d576b3ed78794; source base: 9a74a70a32ebda716a00c7203d8e606343cf442a.

## R24 closure

R24 is CLOSED_INCOMPLETE. Its evidence JSON path is absent and Luna's primary elapsed time has no authenticated receipt. Under R24's unknown-elapsed rule, its 600-second primary cap is conservatively exhausted; no R24 reserve is reused. The exact prior current state, including UNKNOWN workers, root quarantines and R24 leases, is preserved in tasks/agent-loop/history/effect-permission-hygiene-20261030-r24-preclose-current.json (SHA-256 e1080a08f13e8331be89f9c790b65ca135767dcd28f26ceaceda09a210498510). R24's old frozen workspace and outputs remain unchanged.

## Roster and process reconciliation

The live collaboration roster was synchronized before admission. The R24 Rust author and reviewer, Lean author, and other registered children were completed/stopped; no child was running. Process inspection found no Cargo, rustc, Lake, or Lean process. No capacity override or unknown-path lease release was used. Existing UNKNOWN worker rows, quarantine paths, and the recorded user capacity override remain intact.

The R25 Rust implementer is waiting for the pushed admission ACK. The nonauthor reviewer is reserved and waiting for a frozen target. No child has been resumed, no Cargo or Lean process has started, and no R25 source file has changed.

## Exact source intake

Luna created detached worktree isolated/ep-hygiene-r25/project at 9a74a70a32ebda716a00c7203d8e606343cf442a. It was clean at intake. All eight rust_baseline entries in the input manifest were independently matched against the Git blobs and the new worktree. The runtime source SHA-256 values are machine.rs 4fe3de685650761767be313285321e548964b41900c3aae7f5f434d48034395d; receiving.rs e6b22598a0d11a21fba260cdbc5b4ace3690cf9b21e51beb61d8cc967511fffd; program.rs 6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907. Cargo manifests, lockfile, runtime mod.rs, and the companion example also match. No R24 overlay or root quarantined source was used.

## Resource ledger at admission

Fresh envelope: Rust 2,600 seconds; independent review 1,800 seconds; Luna primary 1,200 seconds; Astra 0. Luna primary accounting starts at 2026-10-29 19:05:46 UTC with 0/1,200 seconds charged and 1,200 seconds remaining. Rust and review clocks remain at zero until their respective actual resume/assignment receipts. The two Cargo gates and their exact-hash review reservations remain separate as specified by the contract.

Exact R25 write leases are the six paths in the contract and current.json. The R24 leases have been archived as frozen evidence; root UNKNOWN_WRITER runtime paths remain quarantined and untouched.
