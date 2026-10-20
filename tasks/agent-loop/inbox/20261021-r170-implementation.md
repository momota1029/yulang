# R170 bounded native tuple observation — Luna implementation assignment candidate

Status: candidate only; no code lease or probe authorization until the exact R170 contract/handoffs receive prospective CLEAN review and Luna records a fresh activation receipt.

Contract: `tasks/agent-loop/sprints/provider-capture-incidence-20261021-r170.md`; revision 1 candidate.

Goal: extend R169's borrowed observation to already-retained Capture bounds/snapshots and provider-owned maps in the exact contract owners, then consume it from one Rust example over the existing `tools/inference-playground/examples/entry-computation-argument.yu` fixture. This is provisional source evidence, not a semantic consumer, inference certificate or Yulang2 coverage.

Proposed exact code leases:

- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `tools/inference-playground/examples/r170_provider_incidence.rs`

Read-only source fixture: `tools/inference-playground/examples/entry-computation-argument.yu`.

Exact evidence receipts: `notes/theory/2026-10-21-r170-native-tuple.md`, this handoff, and `tasks/agent-loop/probes/20261021-r170-provider.{stdout,stderr,status}`. A single in-repository Cargo run is only authorized after exact code/source review and activation; build artifacts remain in the repository's normal `target/` tree. No Yulang2 execution, web sample, test suite, retry, external runtime, `/tmp`, alternate checkout, nested CLI, network or background service.

Required implementation behavior: borrow existing retained structures only; preserve order and alternatives; expose unavailable joins explicitly; cap output; do not create solver state or alter inference. If the association requires a new owner or persistent record, stop and return the missing owner. Never label the observation a unique historical event or source-fact join unless the records establish it.

Proposed Luna allocation 1500 seconds plus one 300-second build/probe ceiling within 4800 total, no carryover. Fresh independent review belongs to a non-author coauthor. Exact source/artifact hashes, diff, command, stdout/stderr/status, noninterference limits, review and writer stop belong in the frozen result. Luna alone owns Git.
