# R109 admission

Admitted after the R108 source compile gate stopped with `NO_SAFE_COMPILE_SLICE` and the sprint selector recommended recovering the full R105 `candidate_effect.rs` artifact before any further compile attempt.

Objective is limited to read-only provenance recovery of `crates/yu-solver/src/candidate_effect.rs`. Baseline R108 commit: `54526ec9514b7065c7d7460702e9d6e2ecbc0842`. Exact write lease is only `tasks/agent-loop/inbox/effect-permission-effect-baseline-recovery-r109.md`; one implementer ≤300 seconds followed by fresh compiler_referee ≤180 seconds. No source edits, builds/tests, materialization, scratch, cache, worktree, environment, Git mutation, stage or push. Preserve UNKNOWN workers, quarantines and unrelated dirty paths.
