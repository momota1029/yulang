# EFFECT-PERMISSION-GRAPH-FIXTURE-REPAIR/20261101-R102

Status: admitted after R101's focused Cargo gate failed before tests. R101 is closed failed with 1/1 calls consumed; no retry.

## Fixed outcome and source evidence

Update two test-only hand-written `Graph` initializers for the new `lambda_argument_effects` field, then obtain independent review and one focused observer suite result. R101's effect-observer candidate and R99's Member ownership fix remain unchanged.

R101 stderr reports E0063 at `shadow_apply.rs:4956` and `:5070`; both `Graph` values have `nodes: Vec::new()` and are row-identity fixtures. The field declaration at `candidate_scheme.rs:201` stores registration labels attached to actual Function nodes. Normal capture construction starts it empty at `candidate_scheme.rs:2788` and appends only when a retained Function node and argument-effect child are found at `:2961+`. These fixtures contain no Function node; the correct value in each is `lambda_argument_effects: Vec::new()`. Do not synthesize/copy inference registrations or alter assertions/semantics.

## Frozen snapshot and leases

Branch `yulang3`, baseline HEAD `d0829f48a`. Exact current candidate inputs (some intentionally dirty relative to HEAD):
- Writable `crates/yu-solver/src/shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`, limited to the two named test-only Graph initializers.
- Read-only `crates/yu-solver/src/candidate_effect.rs`: `536942ff167cdd869c5a3a9eade852453bde6c9f53a5e64023194e681d1cebe6`.
- Read-only `crates/yu-solver/src/candidate_receiver.rs`: `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`.
- Read-only `crates/yu-solver/src/lib.rs`: `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f`.
- Read-only `crates/yu-solver/src/candidate_scheme.rs`: `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631`.
- `Cargo.toml`: `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a`; `Cargo.lock`: `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`; solver manifest: `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`.

One exact handoff: `tasks/agent-loop/inbox/effect-permission-graph-fixture-repair-source.md`. No other write paths, unknown leases or quarantines are released. Primary owns all Git.

## Review and execution gates

Implementer `/root/rust_observer_repair` Luna/high <=300 seconds. A fresh independent compiler referee <=500 seconds reviews the complete five-file candidate, both fixture initializers and all protected tests before execution; same reviewer assesses execution receipt. Primary <=700 seconds, total <=1,500 seconds, Astra 0.

Only after review PASS, run one command:
`cargo test --locked --offline -p yu-solver --features shadow-apply-candidate candidate_effect::tests:: -- --test-threads=1`
Use one CPU, <=180 seconds, <=2 GiB RSS, unique `/dev/shm/yulang-effect-permission-graph-fixture-repair-20261101-r102-target` capped at 8 GiB. Probe exact-path write/execute/cleanup first; no ext4 target, downloads, retry or persistent target. Save command/source/dependency hashes, complete logs, exit/time/RSS, sampled target peak, and cleanup result to R102 history before removing only that target.

Success requires exact empty-vector field initialization, pre-execution review PASS, focused tests exit 0, receipt review PASS, and primary verification of the full outbound range. Any failed gate closes R102 without code push. No Lean theorem, source/native bridge, semantic approval or production permission is closed; preserve R95 and all unknown/quarantine state.
