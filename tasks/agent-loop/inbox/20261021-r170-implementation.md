# R170 bounded native tuple observation — Luna implementation assignment candidate

Status: candidate revision 2 only; revision 1 was committed under `20cfd4ccd` and returned for one major execution-spec finding. No code lease or probe authorization until the exact revised R170 contract and both handoffs receive prospective CLEAN review and Luna records a fresh activation receipt.

Contract: `tasks/agent-loop/sprints/provider-capture-incidence-20261021-r170.md`; revision 2 candidate. Revision 1 contract hash: `57b517516c524839ff174f0aaf08aaa163e2a6055bb84fd61c03246522fb5234`.

Goal: extend R169's borrowed observation to already-retained Capture bounds/snapshots and provider-owned maps in the exact contract owners, then consume it from one Rust example over the existing `tools/inference-playground/examples/entry-computation-argument.yu` fixture. This is provisional source evidence, not a semantic consumer, inference certificate or Yulang2 coverage.

Proposed exact code leases:

- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `tools/inference-playground/examples/r170_provider_incidence.rs`

Read-only source fixture: `tools/inference-playground/examples/entry-computation-argument.yu`, SHA-256 `a81a52d582067e9d76ca41bfb946cd539cd98cc369b9b2c2a01fb0b3e0e239fd`.

Exact evidence receipts: `notes/theory/2026-10-21-r170-native-tuple.md`, this handoff, and `tasks/agent-loop/probes/20261021-r170-provider.{stdout,stderr,status}`. A single in-repository Cargo run is only authorized after exact code/source review and activation; build artifacts are confined to `target/r170/`. No Yulang2 execution, web sample, test suite, retry, external runtime, `/tmp`, alternate checkout, nested CLI, network or background service.

Required implementation behavior: borrow existing retained structures only; preserve order and alternatives; expose unavailable joins explicitly; cap output; do not create solver state or alter inference. If the association requires a new owner or persistent record, stop and return the missing owner. Never label the observation a unique historical event or source-fact join unless the records establish it.

Proposed Luna allocation 1500 seconds plus one 300-second build/probe ceiling within 4800 total, no carryover. The exact one-time invocation after fresh independent source/code review is `CARGO_TARGET_DIR=target/r170 cargo run --offline --locked --manifest-path tools/inference-playground/Cargo.toml --example r170_provider_incidence`, from repository root, with no other environment overrides or arguments. Explicit generated writes are confined to `target/r170/` and the three exact probe receipt paths; Cargo registry/cache must remain read-only. Fresh independent review belongs to a non-author coauthor before the probe and again at final closeout as needed. Exact source/artifact hashes, diff, command, stdout/stderr/status, noninterference limits, review and writer stop belong in the frozen result. Luna alone owns Git.
