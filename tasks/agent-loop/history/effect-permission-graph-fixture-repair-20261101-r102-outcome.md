# R102 outcome and execution receipt

Status: `CLOSED_FAILED_TESTS_REVIEWED`; the one authorized Cargo invocation failed with five tests, and the independent execution-receipt review passed.

Contract SHA-256: `b36fc969c72cd1768e9b06d75382e312e4c2c5e54dd68874b8ebd8166ef15e12`.
Admission SHA-256: `a5676ecfae4129ac836c33f44a5ce90026b301361ecab5a1c8f44476ab172e50`.

## Independent pre-execution review

Fresh compiler-referee `/root/r102_fresh_review`: PASS, no blocking/major/minor findings. It confirmed exact five-file hashes; R102 delta is only the two admitted empty-vector field initializations; both fixtures have `nodes: Vec::new()`, and no assertions/semantics changed. Protected tests and observer joins remain intact. Static review only; STOPPED, no descendants.

## Frozen component and dependencies

- `crates/yu-solver/src/shadow_apply.rs` SHA-256 `caeb837cd13b2e75e76fbed59dcc601e8c9d0a6a6a6f56f6959c0b0b9a98007f`
- `crates/yu-solver/src/candidate_effect.rs` SHA-256 `536942ff167cdd869c5a3a9eade852453bde6c9f53a5e64023194e681d1cebe6`
- `crates/yu-solver/src/candidate_receiver.rs` SHA-256 `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`
- `crates/yu-solver/src/lib.rs` SHA-256 `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f`
- `crates/yu-solver/src/candidate_scheme.rs` SHA-256 `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631`
- `crates/yu-hir/src/module.rs` SHA-256 `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`
- `Cargo.toml` SHA-256 `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a`
- `Cargo.lock` SHA-256 `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`
- `crates/yu-solver/Cargo.toml` SHA-256 `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`

## Exact authorized invocation

Command SHA-256: `d31e468d477bf9ad003313f7b67f5921b709581790076f35e731919f442db905`.

```text
CARGO_TARGET_DIR=/dev/shm/yulang-effect-permission-graph-fixture-repair-20261101-r102-target CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=1 timeout 180s taskset -c 0 /usr/bin/time -v cargo test --locked --offline -p yu-solver --features shadow-apply-candidate candidate_effect::tests:: -- --test-threads=1 > tasks/agent-loop/history/effect-permission-graph-fixture-repair-20261101-r102-verification.stdout 2> tasks/agent-loop/history/effect-permission-graph-fixture-repair-20261101-r102-verification.stderr
```

stdout/stderr and the sampled peak receipt are retained at the exact history paths. The unique `/dev/shm` target write/execute/cleanup probe passed. No ext4 target, persistent cache or retry was used; the target is absent after cleanup.

## Final invocation result

The one authorized Cargo call exited **101** after **102.16 seconds**. Tests ran: **45 passed, 5 failed, 2 ignored, 771 filtered out**. Maximum RSS **1,719,752 KiB**, swaps 0. Sampled `/dev/shm` target peak **4,073,771,379 bytes**, under the 8 GiB cap; target directory is absent and no Cargo/rustc descendants remain.

Failures:
- `formal_and_whole_annotation_share_tail_in_the_returned_effect_fiber`: `candidate_effect.rs:4879`, `session.errors.is_empty()` false.
- `formal_permission_constructor_owner_domain_graph_export_join`: `candidate_effect.rs:3821`, expected unequal raw allocation/captured representative; observed `[(21,21),(23,23)]`.
- `formal_permission_consumer_residual_observation`: `candidate_effect.rs:3844`, no returned SupportView state node; trace printed `consumer-returned-effect-forms=[]`.
- `formal_permission_symbolic_effect_memo_trace_tolerates_missing_constructor_identity`: `candidate_effect.rs:3518`, otherwise-equal state debug strings differed only by `TermArenaBrand(25)` versus `(26)`.
- `views_keep_fresh_use_ownership_and_intrusion_rollback_restores_relations`: `candidate_effect.rs:5613`, routes lacked a positive Support endpoint.

Complete stdout (8,691 bytes) SHA-256 `4e5f70917e6eb42e273942eaa8b4d4fa9803f0d1e3f46d8ef0adbc7cd909a4d2`; stderr (33,888 bytes) SHA-256 `59187ed309458c9f9227330f58c8f5fd7686123cca71be230a1c7c18e841340a`; sampled target-peak receipt SHA-256 `751e038d6ffd4704b74f6db71133cd61fc194db107dcf341f437811c3fe8e695`. Command SHA-256 remains `d31e468d477bf9ad003313f7b67f5921b709581790076f35e731919f442db905`.

R102 closes failed after its single test call. The same independent reviewer returned receipt PASS for the exact logs, hashes, resource measurements and cleanup; execution remains failed, so no Rust source push follows. No theorem, source/native, semantic or production gate is closed.
