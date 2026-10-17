# NPAIR source/call owner handoff

On 2026-10-18 the user directly confirmed the inherited source/call writer is stopped: “停止しています！” This is the primary STOP evidence for the two quarantined paths in `tasks/agent-loop/current.json`.

## Descendants, outputs and overlap

- The live collaboration tree was reconciled at handoff: no active legacy source/call writer or descendants are present. Current-session review and proof children are completed, with their receipts stating no source/call writes or descendants.
- The compact lease inventory names only `crates/yu-solver/src/candidate_source.rs` and `crates/yu-solver/src/candidate_call.rs` under the inherited source/call writer. The related archived owner records were checked: the dispatcher board lease is frozen, the idle implementer has no task/output lease, and the prior proof output is frozen with no successor lease.
- The worktree was clean before this handoff. No untracked generated output or live overlapping writer was present. Other legacy UNKNOWN reservations remain quarantined; this receipt transfers only the two source/call paths below.

## Transfer

Luna accepts the stopped-owner handoff and grants a new **read-only** lease on exactly:

- `crates/yu-solver/src/candidate_source.rs`
- `crates/yu-solver/src/candidate_call.rs`

The lease is for the bounded NPAIR source-to-action audit. It does not authorize code edits, expected-output changes, production promotion, or access to paths outside a separately recorded sprint contract. Fresh hashes are captured only after this handoff.

Original source/native parent closure remains **0**. The adopted concrete-only source-admission decision is in force and will not be asked for again.
