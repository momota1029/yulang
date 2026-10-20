# R170 bounded native tuple observation — Luna implementation assignment candidate

Status: candidate revision 4 only; revision 1 is at `20cfd4ccd`, revision 2 at `e9d3a1367`, and revision 3 at `74d11fa38`; rev3 returned for network-isolation and timeout/cessation findings. No code lease or probe authorization until the exact revised R170 contract and both handoffs receive prospective CLEAN review and Luna records a fresh activation receipt.

Contract: `tasks/agent-loop/sprints/provider-capture-incidence-20261021-r170.md`; revision 4 candidate. Revision 1 contract hash `57b517516c524839ff174f0aaf08aaa163e2a6055bb84fd61c03246522fb5234`; revision 2 hash `45092451735aea21006c46f3b1e479a2a8405b7a1a98c6ab04eec39f99409394`; revision 3 hash `9aee566e2275d065d2c85986bd78ab040bba7aaf34998ee0478a082bcfd1e3b6`.

Goal: extend R169's borrowed observation to already-retained Capture bounds/snapshots and provider-owned maps in the exact contract owners, then consume it from one Rust example over the existing `tools/inference-playground/examples/entry-computation-argument.yu` fixture. This is provisional source evidence, not a semantic consumer, inference certificate or Yulang2 coverage.

Proposed exact code leases:

- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `tools/inference-playground/examples/r170_provider_incidence.rs`

Read-only source fixture: `tools/inference-playground/examples/entry-computation-argument.yu`, SHA-256 `a81a52d582067e9d76ca41bfb946cd539cd98cc369b9b2c2a01fb0b3e0e239fd`.

Exact evidence receipts: `notes/theory/2026-10-21-r170-native-tuple.md`, this handoff, and `tasks/agent-loop/probes/20261021-r170-provider.{stdout,stderr,status}`. A single in-repository Cargo run is only authorized after exact code/source review and activation; build artifacts are confined to `target/r170/`. No Yulang2 execution, web sample, test suite, retry, external runtime, `/tmp`, alternate checkout, nested CLI, network or background service.

Required implementation behavior: borrow existing retained structures only; preserve order and alternatives; expose unavailable joins explicitly; cap output; do not create solver state or alter inference. If the association requires a new owner or persistent record, stop and return the missing owner. Never label the observation a unique historical event or source-fact join unless the records establish it.

Proposed Luna allocation 1500 seconds plus one 300-second build/probe ceiling within 4800 total, no carryover. The contract's one-time invocation uses `/usr/bin/bwrap --unshare-net` with host root read-only and writes only to `target/r170/` plus exact receipts; GNU `timeout` bounds the command group and a bounded `/proc` scan checks cessation. Cargo runs offline and locked from the repository root. Fresh independent source/code review must CLEAN exact code and example hashes before the probe; final review remains independent of Luna. Exact source/artifact hashes, diff, command, stdout/stderr/status, noninterference limits, review and writer stop belong in the frozen result. Luna alone owns Git.
