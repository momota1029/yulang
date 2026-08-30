# Historical yulang2 `infer` test memory incidents

> Historical yulang2 incident; not an active yulang3 command policy.

The commands, crate names, skip patterns, test names, and memory observations below describe the old yulang2 workspace. The current yulang3 workspace has no `infer` member. Preserve this record for root-cause and test-runner design lessons; do not copy its skip list into current agent prompts.

## 2026-07-31 — debug safety check reproduced the hot-path cost

An unscoped debug `cargo test -p infer --lib` crashed WSL2 twice. A debug cross-check, `debug_assert_qualified_carrier_index_matches_linear_scan`, ran on every claim-parent insertion. Each invocation linearly rescanned `claim_parents_by_constraint` and allocated a fresh `FxHashSet`. At hundreds of thousands to millions of insertions, the safety net reproduced the unbounded rescan/allocation pattern that the optimization work was meant to remove.

Fix: commit `e76d70ca` made the check `cfg(test)`-gated and invoked only by its dedicated test rather than every production-path insertion.

Lesson: debug/test assertions on a hot path require the same call-volume analysis as production code.

## 2026-08-02 — four test threads were not enough under a regression

An unscoped `cargo test -p infer` with `--test-threads=4` ran for more than eight hours and reduced available memory to about 900 MiB before termination. Full-std/characterization and acceptance suites became extremely expensive when a solver regression was present.

The historical mitigation used focused module filters and skipped known heavy names such as `repository_std`, `real_std`, `cprov_a`, `cprov_h`, `sound_a`, `stage0_characterizes`, `stage2_snapshot`, `shadow_dirty_oracles_characterize`, and `stage6_`. Four known failures were also tracked at that time. Those names are recorded only to reconstruct the incident; they are not a yulang3 test recipe.

Lesson: concurrency caps do not make an algorithmic regression safe, and a broad filtered command must be designed from the current test inventory.

## 2026-08-02 — RCPF-C3a module-filter mistake

A run of `cargo test -p infer --lib lowering:: -- --test-threads=4` omitted the historical skip list under the false assumption that the heavy tests belonged only to another module. Several heavy `lowering::body` suites ran concurrently. RSS reached roughly 30 GB, about 91.9% of system memory, with swap around 3.7 GB. The process was killed and memory recovered immediately.

Lesson: test-name location and module filters must be verified. A remembered skip list is fragile and should be encoded in a safe runner only after current inventory analysis.

## 2026-08-04 — the known skip list was incomplete

An intentionally broad `cargo test -p infer --lib` with the then-standard skip patterns and four threads reached about 24 GB RSS (roughly 73% of memory) after about 32 minutes. Four individually heavy tests not present in the known list ran concurrently, including analysis, stage0, yumark, and lowering cases. Termination restored about 28 GB available memory.

Lesson: a hand-maintained list catches only previously observed tests. A truly broad run needs serial execution or active resource monitoring and a kill condition; even that is not a substitute for fixing pathological work.

## Environment decision at the time

The user declined a global `.wslconfig` memory cap and accepted occasional crashes rather than adding that system-level setup. This was an environment-specific decision for the old workspace, not a standing prohibition on current resource safeguards.

## Durable conclusions

- Start with the smallest relevant test.
- Account for debug/test-only work on hot paths.
- Do not infer suite safety from a thread cap or stale skip list.
- Investigate current test inventory before a broad run.
- Prefer a reviewed deterministic verifier over prompt-copied command folklore.
