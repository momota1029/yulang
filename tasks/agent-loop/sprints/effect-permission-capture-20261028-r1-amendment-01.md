# Sprint EFFECT-PERMISSION-CAPTURE-20261028/r1 amendment 01

Status: ADMITTED by primary after next-action selector consultation.

Parent contract: `tasks/agent-loop/sprints/effect-permission-capture-20261028-r1.md`,
SHA-256 `5150233fa70a25ab5afb960a00bc18620bc645f030026dc19a1a1a9168daa93a`.
Sprint baseline remains `yulang3` at `233b221d6`; the frozen Rust source remains
`crates/yu-solver/src/shadow_apply.rs`, SHA-256
`2e0aba4d172e97dd60ba909a7aca873c109785f3d38cce46ddd033c70f64613d`.

## Reason and exact change

The first authorized focused Cargo invocation was:

```text
CARGO_TARGET_DIR=/tmp/yulang-effect-permission-capture-20261028-r1/rust-target
CARGO_BUILD_JOBS=1 taskset -c 0 cargo test -p yu-solver --lib formal_permission -- --nocapture
```

It exited 101 during test compilation because it omitted the existing
`shadow-apply-candidate` feature. No test executed and no source was changed.
Preserve that failed attempt and its log as evidence.

Authorize exactly one corrected invocation by increasing this Rust lane's
heavyweight invocation maximum from one to two. The retry uses the same focused
filter and existing target directory, adding only
`--features shadow-apply-candidate`:

```text
CARGO_TARGET_DIR=/tmp/yulang-effect-permission-capture-20261028-r1/rust-target
CARGO_BUILD_JOBS=1 taskset -c 0 cargo test -p yu-solver --lib --features shadow-apply-candidate formal_permission -- --nocapture
```

Before launch, the primary confirms that the first Cargo process and all child
processes have ended and records that the serialized verification slot is free.
Use one CPU, at most 1 GiB RSS, a 240-second process cap, and the existing
`/tmp/yulang-effect-permission-capture-20261028-r1/rust-target/` only. Do not
change source or tests. Authenticate the frozen Rust source and handoff hashes
before and after the invocation, preserve the first failure, and record exact
argv, exit, elapsed time, RSS if observed, and executed test names/count.

## Resource and stop boundary

The sprint remains capped at 3,600 active-work seconds. This exact retry may
consume at most 240 seconds and primary/dispatcher accounting or reconciliation
may consume at most 60 seconds; charge the full 300-second contingency. This is
the only extra heavyweight attempt. It grants no automatic renewal, further
retry, source edit, feature/API/semantic change, or new lease. Stop with Rust
verification INCOMPLETE on timeout, resource failure, test/build failure, or
artifact hash change. No second corrected attempt is authorized.

The independent reviewer remains read-only and must include the corrected
invocation outcome if available within the existing review cap. Its final
message is the independent review source; because the registered
`compiler_referee` role is read-only, Luna records a clearly labeled primary
transcription in the leased review path, preserving reviewer identity and exact
message provenance. No source/native, parent effect-hygiene, soundness,
principality, termination, or production gate changes status under this
amendment. The actual constructor/live-capture bridge remains OPEN.
