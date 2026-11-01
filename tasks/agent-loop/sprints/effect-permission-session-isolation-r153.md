# R153 — exact source-only integration of the reviewed session binder

Status: admitted continuation under the existing user goal and exact source-only authorization below. This packet turns the reviewed R152 candidate into one uncompiled source checkpoint if the fresh integration review passes.

## Authority and immutable inputs

The user explicitly asked for Rust implementation analysis through push and has standing authorization for coherent, reviewed source checkpoints. Existing repository precedent records narrow source-only authorizations for R111, R132 and R133. R152's contract allowed only an unapplied artifact; this R153 revision supersedes that boundary for this exact candidate only.

Current HEAD baseline: `8be4d4bddff621262ea3f2a1829222f38b076d21`. The three committed source blobs at this baseline have these SHA-256 values, matching R152's frozen baseline:
- `crates/yu-solver/src/candidate_effect.rs`: `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01`
- `crates/yu-solver/src/candidate_scheme.rs`: `e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814`
- `crates/yu-solver/src/shadow_apply.rs`: `2fa42a5570e660babab5da6361e0d71e0c022b234a21f7e01b78eafbfc65f278`

Sole candidate input: `tasks/agent-loop/inbox/effect-permission-session-isolation-r152.patch`, SHA-256 `3a5a2f73b75cd3caaecae7fbb0f36c60b9c33492502fe531f3e7237fdb9838c4`. R152 source handoff: `a18dc477d33e639b002cd22d4825e56640c7ab6c25b0a1f4eebc61974c58094c`; independent R152 review: `06d4aef333b67986454ce234a7a57c335549394c5b5fb90ab6a1e6f150ac2914`; R152 outcome: `0ef2328f1a629ef7dfaac16fb9d01525c10fbab56f9f83eadca8ea123b1cbf96`.

## Exact authorization and limits

Authorize a normal source-only commit and push on `yulang3` for exactly the three source-file changes encoded by the frozen R152 candidate patch. The patch must apply to the committed index at the baseline above, and the full staged source diff must contain only those three paths and match the patch. Keep the source uncompiled and untested in the commit message and outcome. This authorization does not follow from R152 review alone; it is this explicit, versioned R153 authority based on the user's push request.

Do not stage the existing worktree changes. In particular, `candidate_receiver.rs` remains excluded because its dirty diff removes owner/batch/live-state, provider/arm and permission-origin checks. `tools/inference-playground/src/runtime/machine.rs` and `receiving.rs` remain quarantined. All unrelated dirty and untracked paths stay untouched.

No source-only claim closes compilation, behavior, Rust-to-Lean correspondence, INITIAL-STATE, CONSUMER, effect hygiene, soundness, principality, termination, original A/B, or production. No handler, consumer or receiver semantics are changed by this authorization.

## Review and integration

Fresh independent `compiler_referee`, at most 300 seconds, reviews the source-only authority against R152, verifies the exact committed source baseline and frozen patch identity, confirms the patch has no dependency on excluded receiver/runtime changes, and checks that a source commit cannot be mistaken for compile or production approval. Exact output: `tasks/agent-loop/history/effect-permission-session-isolation-20261102-r153-integration.md`.

If review passes, Luna may apply the exact candidate to the index only, verify all three resulting staged blob hashes and the complete outbound range, then commit and push normally. Do not apply it to or rewrite the dirty working tree. Any hash mismatch, additional required file, receiver/runtime dependency, or review finding suspends source integration; preserve R152's pushed unapplied artifact and record the blocker. Build, tests, Lean, environment, scratch, cache and worktree creation: zero.

Resource ceiling: reviewer 300 seconds; primary integration 180 seconds; total 600 seconds. No descendants.
