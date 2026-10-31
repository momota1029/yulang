# R111 admission

Admitted after R110 failed to recover the pre-R106 dirty snapshot and the selector recommended a fresh baseline-derived minimal compile-repair component, ending historical recovery. User's Rust implementation analysis/push authorization remains active.

Exact component: three repaired files only (`lib.rs`, `candidate_receiver.rs`, and baseline `candidate_effect.rs` import); immutable baseline source commit `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`. Source author writes only `tasks/agent-loop/inbox/effect-permission-baseline-compile-repair-r111.md`. No live source writes until compile receipt and independent review pass.

Verification is one offline Cargo `--no-run` invocation inside a temporary private mount namespace with a hard 6-GiB tmpfs aggregate cap, only after fresh pre-review. Source closure must be ≤64 MiB. If user/mount namespace or verified cap is unavailable, stop without compile. No worktree, persistent cache, disk copy, build retry, or test execution. Primary-only exact-blob staging/commit/push after fresh post-run review.
