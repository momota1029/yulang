# R153 exact source-only integration authorization

## User authority

The user's explicit request is to analyze the Rust implementation and take it through push, under the standing authorization for coherent reviewed Rust/Lean checkpoints. Existing repository precedents record versioned source-only checkpoints at R111, R132 and R133. R152's review approved its candidate as unapplied research only; this separate R153 disposition supplies the additional source-integration authority after an independent scope review.

## Narrow target

This authorization covers only the exact reviewed R152 candidate patch:

- Baseline: `8be4d4bddff621262ea3f2a1829222f38b076d21`.
- Patch: `tasks/agent-loop/inbox/effect-permission-session-isolation-r152.patch`, SHA-256 `3a5a2f73b75cd3caaecae7fbb0f36c60b9c33492502fe531f3e7237fdb9838c4`.
- Sole paths: `crates/yu-solver/src/candidate_effect.rs`, `crates/yu-solver/src/candidate_scheme.rs`, `crates/yu-solver/src/shadow_apply.rs`.
- Baseline file SHA-256: `candidate_effect.rs` `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01`; `candidate_scheme.rs` `e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814`; `shadow_apply.rs` `2fa42a5570e660babab5da6361e0d71e0c022b234a21f7e01b78eafbfc65f278`.
- R152 independent review: PASS for exact candidate only, review SHA-256 `06d4aef333b67986454ce234a7a57c335549394c5b5fb90ab6a1e6f150ac2914`.

After the independent R153 integration review passes, Luna may apply the exact patch to the Git index, verify the complete staged diff and resulting blobs, then commit and push normally. Do not modify or stage the dirty worktree. If any target hash, candidate dependency, path, or patch application differs, stop source integration and keep the pushed R152 artifact only.

## Claims kept open

The source checkpoint must be labeled uncompiled and untested. This authorization establishes no compile/runtime result, source/native correspondence, INITIAL-STATE, CONSUMER, effect hygiene, soundness, principality, termination, original A/B, or production readiness. The dirty `candidate_receiver.rs` delta is expressly excluded, as are quarantined runtime files and every other dirty/untracked path. No new environment, cache, scratch or worktree is authorized.
