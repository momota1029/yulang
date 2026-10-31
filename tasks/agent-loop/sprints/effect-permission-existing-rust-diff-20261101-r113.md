# EFFECT-PERMISSION-EXISTING-RUST-DIFF/20261101-R113

Status: admitted after R112 closeout. This sprint responds to the user's explicit request to analyze existing Rust work toward a pushable implementation checkpoint. It classifies the current dirty solver delta without modifying source.

## Fixed outcome

Using the current `HEAD` as the committed comparison point, freeze and classify the existing six-file delta in `crates/yu-solver/src/{lib.rs,candidate_receiver.rs,candidate_effect.rs,candidate_scheme.rs,candidate_source.rs,shadow_apply.rs}`. Identify authorship/cessation evidence where available, exact coherent hunks, producer-to-consumer closure, protected expectations, transitive source dependencies, and a safe commit boundary—or report `NO_SAFE_CODE_SLICE` with the first missing fact. Reuse R111's reviewed candidate evidence for the baseline `lib.rs`/receiver/effect repair; do not reconstruct candidate patches.

Preserve `candidate_scheme.rs` as FROZEN and read-only. Runtime `machine.rs`/`receiving.rs`, all UNKNOWN/quarantined paths, and isolated source are out of scope. No source edit, stage, build, compiler, Cargo, test, cache, worktree, environment experiment, expected-output edit, or semantics change is admitted. A research artifact may be committed only after independent review; it is not an implementation commit. R111's exact compile gate remains required before Rust source integration or push.

## Leases and review

- One `implementer` authors only `tasks/agent-loop/inbox/effect-permission-existing-rust-diff-r113.md`, with read-only access to the six named files and R111 evidence. ≤360 seconds.
- One fresh independent `compiler_referee` reviews the frozen handoff, ≤180 seconds; no source writes or execution.
- Primary owns source-path reconciliation, central records, exact staging and any research-only Git checkpoint, ≤180 seconds.
- Aggregate cap 720 seconds; Astra 0. No descendants.

Success requires an independently reviewable source snapshot and an exact safe boundary or honest `NO_SAFE_CODE_SLICE`. Neither result waives compilation, the unresolved source-admission/transport premise, any proof gate, or production authority. Do not stage Rust source under this packet.
