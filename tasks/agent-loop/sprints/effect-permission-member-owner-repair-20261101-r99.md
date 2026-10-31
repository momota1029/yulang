# EFFECT-PERMISSION-MEMBER-OWNER-REPAIR/20261101-R99

Status: admitted by Luna under the standing Rust/Lean goal. This is an owner-local continuation after R98-v2 exhausted its two Cargo calls and failed before tests.

## Fixed outcome and evidence

Original goal: advance the approved effect-permission observer implementation while preserving original source domain, A/B claims, semantics and independent Lean/source-native obligations. R99 only repairs the compile-blocking ownership predicate and seeks a reviewed executable candidate. It does not promote production behavior or close a theorem.

R98 final stderr (`tasks/agent-loop/history/effect-permission-rust-observer-compile-repair-20261101-r98-verification.stderr`, SHA-256 `81a78090f0c37fb5ef26284ce5db0ae1d3278afa5c28fd465a2bf4e785b6a388`) reports E0004 at `candidate_receiver.rs:4433`: `SourceRootId::Member(_)` is missing. The canonical `HirModule::owns_source_root(&SourceRootId)` at `crates/yu-hir/src/module.rs:1951` handles Definition, Expression and Member, including artifact/module identity. Replace the partial local match with `local_source.hir.owns_source_root(&registration.owner)`; do not add a wildcard arm or change semantics.

The complete component for review is the five-file observer candidate: writable `candidate_receiver.rs`; frozen read-only `candidate_effect.rs`, `lib.rs`, `candidate_scheme.rs`, `shadow_apply.rs`. Restore assertions in the original nonrecursive regression remain part of the gate and must be reviewed before execution.

## Exact snapshot and leases

Branch/baseline: `yulang3`, HEAD/upstream `b843f897f62f07d521d4127fc32c67645ecd94e8`.

Writable source lease: `crates/yu-solver/src/candidate_receiver.rs`, baseline SHA-256 `03553455bb3b0a4cb0f0ad2fb04b1b8dbf8fac00982547323fe8b6439edbb34d`. Inspect this owner for analogous incomplete `SourceRootId` matches; any additional required edit returns to Luna.

Read-only/frozen source inputs:
- `crates/yu-solver/src/candidate_effect.rs`: `bf7528133a1ebaa0a80434f2bf114d21c06717235575bab45fbf4c5dffc7cb57`
- `crates/yu-solver/src/lib.rs`: `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f`
- `crates/yu-solver/src/candidate_scheme.rs`: `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631`
- `crates/yu-solver/src/shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`
- `crates/yu-hir/src/module.rs`: `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`
- `Cargo.toml`: `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a`
- `Cargo.lock`: `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`
- `crates/yu-solver/Cargo.toml`: `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`

One implementer handoff only: `tasks/agent-loop/inbox/effect-permission-member-owner-repair-source.md`. No other paths, including all quarantined runtime files, are available to the implementer. Git is primary-only.

## Lanes, gates, and resources

Implementation: `/root/rust_observer_repair`, Luna/high, at most 300 seconds. Independent fresh `compiler_referee` review (not a coauthor) covers the complete five-file diff and protected regression before the final command, at most 500 seconds. The same reviewer then assesses the immutable execution receipt without reopening changed sources. Primary owns verification, adjudication, records and Git, at most 700 seconds. Astra 0; total active budget 1,500 seconds.

Exactly one final focused command is authorized after pre-execution review PASS:
`cargo test --locked --offline -p yu-solver --features shadow-apply-candidate candidate_effect::tests:: -- --test-threads=1`
Use one CPU, <=180 seconds, <=2 GiB RSS, and a unique `/dev/shm/yulang-effect-permission-member-owner-repair-20261101-r99-target` capped at 8 GiB. Retain exact argv/command digest, frozen source/dependency hashes, full stdout/stderr, exit status, elapsed/RSS/target peak in this sprint's outcome before removing only that target. No retry, network, ext4 target, or persistent cache. First verify exact tmpfs path write/execute/cleanup access; if unavailable, stop without fallback.

Success requires: exact owner edit; restored protected assertions intact; independent pre-execution review PASS; the single Cargo invocation exits 0 and runs the focused tests; reviewer accepts the receipt; primary confirms outbound range contains only explicit intended Rust files and receipts. Failure at any gate closes R99 failed without a code push; a new invocation requires a new bounded successor.

Proof lane remains R95 incomplete. No Lean run is authorized here; source/native correspondence, effect hygiene theorem and production/semantic gates remain OPEN. No unknown writer, reservation, path quarantine or unrelated dirty file is released or touched. No-goal-dispatcher consultation is repeated inside this fixed owner-local packet; material scope/dependency changes return to Luna and the dispatcher.
