# EFFECT-PERMISSION-OBSERVER-EVIDENCE-REPAIR/20261101-R100

Status: admitted after R99's independent pre-execution review rejected the frozen candidate. R99 is closed failed with 0/1 Cargo calls; no test ran.

## Fixed outcome

Repair only the test observer assertions in `candidate_effect.rs` so the restored protected nonrecursive regression matches the actual negative-root publication event and proves the exact symbolic memo miss/hit/delegated-tail witness relationship. Preserve the original source fixture and expected semantics. No emitter, inference, permission, solver, or production behavior changes.

Review evidence: R99 reviewer found `candidate_scheme.rs:3041` emits `negative-root-publish id=… term=… node=…`, while `candidate_effect.rs:3467–3468` expects `negative-root-publish term=… node=…`, making the assertion impossible. At `candidate_effect.rs:3940`, each hit is compared against a collection that includes itself; at `3950–3951`, delegated tails are only checked for nonempty witnesses. Repair by identifying exactly one miss, requiring it precede every hit, and comparing each hit and delegated-tail witness list to the unique miss list. Keep the exact source-row/domain and capture joins.

## Baseline and leases

Branch `yulang3`; baseline HEAD `f3ec6f1ddd08268482df77f9d89570e2a9874694`.

Writable: `crates/yu-solver/src/candidate_effect.rs`, frozen baseline SHA-256 `bf7528133a1ebaa0a80434f2bf114d21c06717235575bab45fbf4c5dffc7cb57`, limited to the affected test observer/assertion code; exact handoff `tasks/agent-loop/inbox/effect-permission-observer-evidence-repair-source.md`.

Read-only component dependencies:
- `crates/yu-solver/src/candidate_receiver.rs`: `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf` (R99 owner fix retained in candidate)
- `crates/yu-solver/src/lib.rs`: `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f`
- `crates/yu-solver/src/candidate_scheme.rs`: `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631`
- `crates/yu-solver/src/shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`
- `Cargo.toml`: `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a`
- `Cargo.lock`: `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`
- `crates/yu-solver/Cargo.toml`: `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`

Only the primary grants leases and performs Git. No quarantine or unknown path is available. The complete reviewed source component is the five files above; inherited changes must remain within the pinned snapshot.

## Gates and resources

Implementation `/root/rust_observer_repair` Luna/high <=300 seconds. Fresh independent compiler referee (not implementer) <=500 seconds reviews the full five-file component and both protected fixtures before execution, then the immutable execution receipt. Primary <=700 seconds including one verification call and Git; total <=1,500 seconds; Astra 0.

After pre-execution review PASS, exactly one command is authorized:
`cargo test --locked --offline -p yu-solver --features shadow-apply-candidate candidate_effect::tests:: -- --test-threads=1`
Use one CPU, <=180 seconds, <=2 GiB RSS, unique `/dev/shm/yulang-effect-permission-observer-evidence-repair-20261101-r100-target` capped at 8 GiB. Verify exact tmpfs write/execute/cleanup access before use; no ext4 fallback, downloads, retry or persistent target. Retain exact argv/command digest, all component/dependency hashes, complete stdout/stderr, exit/time/RSS and measured peak artifacts in R100 outcome before deleting only that target.

Success requires exact observer checks, pre-execution review PASS, focused tests exit 0, reviewer receipt PASS, and primary verification of the complete outbound range. Any review/test failure closes R100 failed with no code push. No Lean run or theorem/source-native/semantic/production closure is claimed; R95 remains failed/open. No goal or semantic scope change.
