# R39 admission receipt

Sprint: `EFFECT-PERMISSION-COMPUTATION-ENTRY/20261031-R39`, revision 1.  
Contract SHA-256: `c0336d8077d763138c8a15f6dbb954595d11513908e3a1aa6e8ad8116eab70c1`  
Inputs manifest SHA-256: `e9b5643fdb925b0c45760c2e9bc930a82da215facc39ac66cdd2be271318efd1`  
Branch/baseline: `yulang3` / `06f1ce59eac7a953af18f27558ad0dd8b2a97237`; HEAD and `origin/yulang3` matched at admission.

## Selection and decision

`next_action_selector` recommended retaining the concrete computation-formal permission at its actual entry constructor, closing R38's first missing transition while keeping provider arrival and Catch residual as separate OPEN gates. Luna accepts the bounded direction with one correction: complete rollback is not a success condition because the authoritative top-level inference principles reject rollback as a goal. The implementation must prepare and validate the retained record/accounting before publishing that record; on resource failure it may safely discard/terminate the affected private attempt. No restoration of unrelated state or previous capacity is required absent a proved invariant.

The policy is fixed by the user-approved annotation hygiene design: a contravariant concrete annotation grants local permission, not an input-effect upper bound; actual inflow remains constraint-derived; permission alone injects no effect; actual Catch/subtraction is outside R39. No semantic alternatives are reopened.

## Exact leases

- Rust writer `/root/r39_rust`: `crates/yu-solver/src/candidate_effect.rs` plus `tasks/agent-loop/inbox/effect-permission-computation-entry-r39-rust.md`.
- Proof writer `/root/r39_proof`: `notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean` plus `tasks/agent-loop/inbox/effect-permission-computation-entry-r39-proof.md`.
- Fresh independent review: `tasks/agent-loop/inbox/effect-permission-computation-entry-r39-review.md`, Luna-owned after both producer lanes freeze.
- Luna owns contract, manifest, admission, stage ledger, outcome, `current.json`, all adjudication, staging and Git.

The Rust file already contains an 843-line pre-existing diff at the pinned dirty-byte hash in the manifest. That exact snapshot is the writer's base; all pre-existing edits remain preserved, review-distinguished, unstaged and outside this lease's semantic delta. No other Rust file is writable. Existing dirty/untracked workspace files and all 32 pending rows remain untouched. Unknown writers/path quarantines remain UNKNOWN/quarantined.

## Resource and stop envelope

Total 6,000 seconds: Rust 1,600; Lean 1,600; review 1,200; Luna 1,600 including 500 closeout; Astra 0. No renewals or transfers. Same WSL checkout. No environment, worktree, copy, scratch, target/cache, Cargo/Lake, build, test or formatter. Lean uses the pinned toolchain by read-only stdin. Static sprint checker and path-limited diff checks only.

The exact source-owner hashes, R38 proof/review hashes, and pinned Lean toolchain are in the immutable input manifest. R38 closed incomplete at `bc83ada2a` plus push receipt `06f1ce59e`; R39 does not promote R38's conditional Lean model into source execution evidence.
