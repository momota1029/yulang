# R144 admission receipt

Luna admits `EFFECT-PERMISSION-SCOPE-TRANSFORMER-SOURCE-BRIDGE/20261102-R144` against baseline `77cf25096f8271590b89380fc988d7e2dd11e7d6`.

Contract: `tasks/agent-loop/sprints/effect-permission-scope-transformer-source-bridge-20261102-r144.md`.

Exact producer leases:

- Luna/high `implementer`, up to 600 seconds: `crates/yu-solver/src/candidate_scope.rs` test module only, and `tasks/agent-loop/inbox/effect-permission-scope-remap-r144-source.md`.
- Read-only source/proof mapper, up to 300 seconds: `tasks/agent-loop/inbox/effect-permission-scope-remap-r144-proof.md` only.
- Fresh independent `compiler_referee`, up to 240 seconds after both writers stop: `tasks/agent-loop/history/effect-permission-scope-remap-r144-review.md` only.
- Luna owns contract, admission, current state, outcome and all Git operations.

No Cargo, build, test execution, Lean, Lake, scratch, cache, target output, environment or worktree is authorized. The bounded regression candidate may be reviewed and checkpointed only with its uncompiled/unexecuted status explicit. No production behavior or source semantics change is in scope. R143 remains closed as `KERNEL_CHECKED_RESEARCH_ONLY`; its outcome is `tasks/agent-loop/history/effect-permission-ordered-snapshot-kernel-check-20261102-r143-outcome.md`.
