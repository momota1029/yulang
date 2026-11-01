# R132 exact source-only integration authorization

Authority: the user's latest instruction to analyze the Rust implementation
and take it through push, read together with the standing authorization for
coherent Rust/Lean checkpoints. This versioned disposition supersedes the
R132 admission's no-source-write/no-push limit only for the exact candidate
below. It does not generalize R111's authorization or permit unrelated dirty
Rust changes to be staged.

- Sprint: `EFFECT-PERMISSION-ROUTE-REGISTRATION-PROVENANCE/20261102-R132`.
- Baseline: `559021b7157b5f1fea949d08228aad13171d07b8`.
- Sole source path: `crates/yu-solver/src/candidate_scheme.rs`.
- Reviewed complete target: 508,255 bytes, SHA-256
  `9cb8349a6ad43ddde8f54ae04ea464a61781b626b25917e928d45d49de3b2012`.
- Independent review: `tasks/agent-loop/history/effect-permission-route-registration-provenance-20261102-r132-review-r2.md`, PASS with the recorded minor receipt correction.

The authorized operation is to integrate only the exact reviewed additive
adapter from the frozen R2 handoff and push the coherent explicit-path commit
range on `yulang3`. The worktree version of `candidate_scheme.rs` already has
unrelated unstaged edits; preserve them and stage only the patch against the
committed baseline. No other Rust source, test, manifest, lockfile or pending
artifact is included.

The source remains uncompiled and untested. This authorization does not claim
that it builds, is consumed, proves Rust-to-Lean correspondence, closes either
original A/B obligation, establishes effect hygiene, or is production-ready.
Those gates remain OPEN. No compiler/Cargo/test/Lean/checker or environment
probe is authorized by this disposition.
