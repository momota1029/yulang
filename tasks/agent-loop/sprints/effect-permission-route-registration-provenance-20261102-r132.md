# R132 — route/registration provenance from committed Rust baseline

Status: ADMITTED. Parent source-preservation, effect-hygiene and original A/B
obligations remain OPEN.

## Goal

From the committed baseline, construct an exact in-memory minimal Rust candidate
that retains the raw negative Lambda `entry_effect` through capture and
FreshUse, and binds the provisional permission adapter to one
`InferenceSession`. Then establish from the candidate source the actual
provenance path:

`candidate_source` formal registration → `lib.rs` Lambda construction →
`candidate_context::retain_lambda_argument_effect` →
`candidate_scheme` capture → FreshUse row mapping → selected session-owned
route/incidence adapter.

Track raw entry row, canonical representative, graph-row position, freshened
row, registration, Lambda occurrence and retained incidence as distinct
values. Analyze interrupted capture, failure and rollback paths for stale or
cross-Lambda incidence reuse. Numeric equality alone is not provenance.

## Exact baseline and output lease

HEAD at admission: `559021b7157b5f1fea949d08228aad13171d07b8` on `yulang3`, equal
to `origin/yulang3`. Read dependencies only from this commit; ignore and do not
stage the dirty working-tree observer/test diffs. Quarantined
`tools/inference-playground/src/runtime/machine.rs` and `receiving.rs` remain
out of bounds and must not be read.

Frozen committed source SHA-256 pins:

- `crates/yu-solver/src/lib.rs` — `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f`
- `crates/yu-solver/src/candidate_effect.rs` — `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01`
- `crates/yu-solver/src/candidate_receiver.rs` — `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`
- `crates/yu-solver/src/candidate_scheme.rs` — `064df99d57aa657f6f1491f16b249403d2ee155b36142e15ca67cafb070df070`
- `crates/yu-solver/src/candidate_source.rs` — `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`
- `crates/yu-solver/src/candidate_context.rs` — `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`
- `crates/yu-solver/src/candidate_call.rs` — `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`
- `crates/yu-solver/src/candidate_intrusion.rs` — `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`
- `crates/yu-solver/src/term.rs` — `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`

Sole worker output lease:
`tasks/agent-loop/inbox/effect-permission-route-registration-provenance-r132-source.md`.
It must contain the complete applicable unified patch, old/target byte counts
and SHA-256, exact owner/field mapping, source locations for every transition,
failure/rollback analysis, first missing source equation and explicit stop
receipts. No source file, index or other artifact is leased.

## Gate and limits

An exact source-level provenance argument and a complete minimal candidate are
required. If the committed owners do not support the path, return the first
concrete obstruction; do not import dirty observer changes or invent guards.
No compiler, Cargo, tests, formatter, Lean, checker, storage/environment probe,
scratch file or source materialization. Reviewer is a fresh independent
`compiler_referee`, 240 seconds, read-only, after the author freezes exact
bytes. Attack two Lambdas in one session, canonicalized unequal rows, repeated
FreshUse, failed/interrupted capture and rollback. No solver or handler
semantics, Catch consumer, theorem or production claim changes. Total primary,
author and review envelope: 1,200 seconds; Astra 0.

R111's source-only authorization applies only to its exact three committed
hashes. R132 output is a new candidate and has no source integration or push
authorization. R131 review does not transfer automatically to new bytes.
