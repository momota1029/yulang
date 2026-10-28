# Frozen verification plan — amendment 04

Authority: primary admission `tasks/agent-loop/inbox/selected-module-entry-freshening-amendment04-admission.md`; independently reviewed three-owner SHA pins are recorded there and in the review receipt. This is M1 focused regression verification of the admitted research candidate.

Exactly two tests, in order:

1. `candidate_effect::tests::tuple_formal_permissions_keep_element_paths_and_transaction_ownership`
2. `candidate_effect::tests::formal_permission_symbolic_effect_memo_trace_tolerates_missing_constructor_identity`

No recursive transport probe or broad filter. The second run occurs only if the first passes. A single outer timeout gives both Cargo invocations 180 seconds maximum in total. A one-CPU taskset, `CARGO_BUILD_JOBS=1`, and the user systemd transient scope enforce one CPU and a 2 GiB memory cap; swap is disabled. The Cargo target and TMPDIR are isolated and leased. `--locked --offline` prevents lockfile mutation and network access. Combined stdout/stderr for each test and supervisor timing go to separate frozen files.

Exact launch command:

```text
systemd-run --user --scope --quiet --property=MemoryMax=2G --property=MemorySwapMax=0 --property=CPUQuota=100% -- /usr/bin/time -v timeout --signal=TERM --kill-after=5s 180s taskset -c 0 env CARGO_TARGET_DIR=/home/momota1029/rust/yulang/isolated/selected-module-entry-freshening-repair-r1/target-amendment04 CARGO_BUILD_JOBS=1 CARGO_NET_OFFLINE=true RUSTC_WRAPPER= TMPDIR=/home/momota1029/rust/yulang/isolated/selected-module-entry-freshening-repair-r1/tmp-amendment04 /bin/bash -c 'cd /home/momota1029/rust/yulang/isolated/selected-module-entry-freshening-repair-r1 && cargo test --locked --offline --manifest-path /home/momota1029/rust/yulang/isolated/selected-module-entry-freshening-repair-r1/crates/yu-solver/Cargo.toml -p yu-solver --lib --features shadow-apply-candidate candidate_effect::tests::tuple_formal_permissions_keep_element_paths_and_transaction_ownership -- --exact --nocapture --test-threads=1 > /home/momota1029/rust/yulang/tasks/agent-loop/verification/selected-module-entry-amendment04/run-01-original-regression.log 2>&1 && cargo test --locked --offline --manifest-path /home/momota1029/rust/yulang/isolated/selected-module-entry-freshening-repair-r1/crates/yu-solver/Cargo.toml -p yu-solver --lib --features shadow-apply-candidate candidate_effect::tests::formal_permission_symbolic_effect_memo_trace_tolerates_missing_constructor_identity -- --exact --nocapture --test-threads=1 > /home/momota1029/rust/yulang/tasks/agent-loop/verification/selected-module-entry-amendment04/run-02-missing-constructor-trace.log 2>&1'
```

Preflight immediately before launch: record UTC time, `MemAvailable` (must be >= 4 GiB), allowed CPU list (must include CPU 0), no other active Cargo process, and that this unique target path is absent or empty. Abort without running if any condition fails. Record supervisor exit, each test result, elapsed time, peak RSS, both raw log hashes, and any omitted checks in `result.md`. No retry or workspace-wide check.
