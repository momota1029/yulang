# R149 admission — member state construction and decoder repair

Admitted by Luna after R148 review and dispatcher recommendation, under the user's continuing whole-Yulang soundness/Effect-hygiene objective. No change to source domain, original H/A/B claims, semantics, production authority, or resource envelope.

## Authority and base

- Baseline: `87dfe33bcd4c572d740dc33b454114b6018a4376`; `HEAD == origin/yulang3` at admission.
- Contract: `tasks/agent-loop/sprints/effect-permission-member-state-r149.md`, corrected SHA-256 `3ef1dfd0acd0720b8256d16d81dcd6233c72466a7a5f5116e68083e8a9ddfd36`.
- Admission-time authentication caught one typo in the `candidate_scheme.rs` hash before either lane read that blob's contents. The contract was corrected to the immutable baseline digest; both lanes were instructed to reauthenticate before continuing. No source semantics were inspected under the mismatched digest.
- R148 review: `19329c147c12678ad37aad5158e9ca25f64ba9db5132a6b5eea0a1d1df0f499f`.
- R148 outcome: `3fdfdf2eff967da81664f17598371cce7ea9169b1da3fb950f9a033320bdde3e`.
- The R148 source/proof boundary, five audited theorem receipts, R118/R119 diagnostics, and cache increase are preserved in those records.

## Roster and dirty paths

Immediately before admission, the live collaboration roster had only `/root` running; all listed prior children were complete. No R148 author/reviewer had an active process or descendant. No stale capacity reservation was released in this admission.

The working tree contains pre-existing dirty solver files `candidate_effect.rs`, `candidate_receiver.rs`, `candidate_scheme.rs`, and `shadow_apply.rs`; runtime `machine.rs` and `receiving.rs` remain quarantined to `UNKNOWN_WRITER`. Additional dirty Lean/research artifacts also remain excluded. They are not R149 inputs, and no R149 worker may read, edit, stage, or claim them. R149 Rust evidence comes only from the exact baseline blobs pinned in its contract. No runtime path, lease, or environment is released or created.

Primary read-only triage of the visible solver diff found instrumentation-heavy work mixed with changes to receiver validation. In particular, the dirty `candidate_receiver.rs` diff removes checks for source/native owner and batch/live-state identity, provider operation identity, selected arm/provider family agreement, and exact internal permission-origin matching. This is working-tree-only, unreviewed evidence; it is not a claim about the committed baseline and is explicitly excluded from any commit. It is a reason to reject that mixed diff as a safe outbound code checkpoint until separately audited and repaired.

## Assignments and resources

1. Source contract: researcher, 600 seconds, one output `tasks/agent-loop/inbox/effect-permission-member-state-construction-r149-source.md`; immutable `git show` reads only; no Rust edits/build/tests.
2. Lean repair: registered `lean_prover`, 600 seconds; only `NativePermissionDecoderR118.lean` may be edited, with one proof handoff. Definitions, theorem types, assumptions, axioms, and imports stay fixed. Use existing Lean 4.35.0 and `.lake`; at most two targeted builds and 240 seconds total; cache growth cap 16 MiB.
3. Fresh compiler referee after both author lanes stop: 300 seconds, one review output. No descendants.

Total maximum: 1,680 seconds. No Astra, new environment, worktree, checkout, scratch/cache directory, Rust mutation, or production promotion. R148 source/proof/review writers are confirmed STOPPED and their outputs are frozen by hash. R148 review/outcome are committed; the two handoffs are still untracked and will be checkpointed separately after this admission. Their lease entries were retired only after confirming writers STOPPED and R148 complete; no source-code or quarantined path lease is affected.

## Gate

R149 may establish an implementation-ready source-state contract and an accepted R118/R119 proof receipt. It cannot establish a reachable source counterexample, close source/native correspondence, prove original A/B, approve semantics, or promote production. A Rust patch requires a separate exact-path admission after independent review of the member/state construction contract.
