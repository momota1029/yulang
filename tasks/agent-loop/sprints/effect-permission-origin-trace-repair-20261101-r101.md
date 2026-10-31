# EFFECT-PERMISSION-ORIGIN-TRACE-REPAIR/20261101-R101

Status: admitted after R100's fresh independent review rejected the candidate before Cargo. R100 closes failed with 0/1 Cargo calls.

## Fixed outcome

Preserve the established `origin occurrence=...` trace prefix consumed by the focused regression while retaining the newer witness and constructor identity fields. The test must still check the exact source occurrence and constructor/domain relationships. Inspect every consumer of this event format within the approved source domain. Preserve R100's negative-root term/node join and unique memo miss, ordered hits, delegated-tail witness checks, and canonical tail-intern joins. Change only the test observer/event formatting as required; no solver/permission/production semantics.

R100 review found the mismatch at `candidate_effect.rs:1934` (emitter begins `origin witness=... constructor=... occurrence=...`) and `:4753` (consumer requires `origin occurrence=`). The test cannot pass with the current emitter. Fresh reviewer also confirmed R100's two other observer repairs are adequate and found no other textual trace-prefix mismatch in the focused module.

## Baseline and leases

Branch `yulang3`; baseline HEAD `33de5af508dc22daaa806bf9ce02984868c41335`.

Writable: `crates/yu-solver/src/candidate_effect.rs`, exact current SHA-256 `114bf61685037e65a7ff5ebb83e089080b7b38433472197eabe7ff1026e03cbc`, limited to the origin event formatting and affected test consumer; one handoff `tasks/agent-loop/inbox/effect-permission-origin-trace-repair-source.md`.

Read-only component inputs:
- `crates/yu-solver/src/candidate_receiver.rs`: `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`
- `crates/yu-solver/src/lib.rs`: `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f`
- `crates/yu-solver/src/candidate_scheme.rs`: `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631`
- `crates/yu-solver/src/shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`
- `crates/yu-hir/src/module.rs`: `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`
- `Cargo.toml`: `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a`
- `Cargo.lock`: `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`
- `crates/yu-solver/Cargo.toml`: `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`

Only primary grants leases and owns Git. No quarantined/unknown path is available.

## Gates and resources

Implementation `/root/rust_observer_repair` Luna/high <=300 seconds. Fresh independent compiler referee <=500 seconds reviews the whole five-file candidate, event producer/consumers and both protected fixtures before execution, then assesses the immutable receipt. Primary <=700 seconds including one verification invocation and Git; total <=1,500 seconds; Astra 0.

After review PASS, exactly one invocation:
`cargo test --locked --offline -p yu-solver --features shadow-apply-candidate candidate_effect::tests:: -- --test-threads=1`
One CPU, <=180 seconds, <=2 GiB RSS, unique `/dev/shm/yulang-effect-permission-origin-trace-repair-20261101-r101-target` capped at 8 GiB. Verify exact tmpfs write/execute/cleanup access before use. No ext4 fallback, network, retry or persistent target. Retain exact argv/command digest, source/dependency hashes, full stdout/stderr, exit/time/RSS, target peak and cleanup in R101 outcome.

Success requires the occurrence prefix and all identity/effect observer invariants intact, independent pre-execution PASS, focused tests exit 0, independent receipt acceptance, and primary review of the complete outbound range. Any failure closes R101 without code push. No Lean, theorem, source/native, semantic or production gate is closed; proof obligations remain open. Existing unknown leases/quarantines remain unchanged.
