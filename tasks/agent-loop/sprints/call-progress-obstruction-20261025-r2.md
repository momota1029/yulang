# LEAN-CALL-PROGRESS-OBSTRUCTION-20261025/r2 — output lease amendment

Status: **FROZEN before author activation**. Baseline: `4866464a5`.
This amendment supplements r1 only by enumerating generated Lean output paths
and changing the active contract revision. The r1 propositions, inputs, budgets,
review gate, stop rules and semantic boundaries remain byte-for-byte governed
by `call-progress-obstruction-20261025-r1.md` (SHA-256
`6020b57d97d0642be5702dafe52efa5fc302165ded16d5e717a159b7e92bee5c`).

## Complete exact path leases

P owns only:

- `notes/theory/lean/YulangClosure/CallViewedForceReachability.lean`
- `tasks/agent-loop/inbox/20261025-call-viewed-force-reachability.md`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallViewedForceReachability.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallViewedForceReachability.ilean`

Q owns only:

- `notes/theory/lean/YulangClosure/CallViewedForceStuck.lean`
- `tasks/agent-loop/inbox/20261025-call-viewed-force-stuck.md`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallViewedForceStuck.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallViewedForceStuck.ilean`

Luna owns only:

- `notes/theory/lean/YulangClosure/CallProgressObstruction.lean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallProgressObstruction.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallProgressObstruction.ilean`
- `notes/theory/lean/.lake/call-progress-obstruction-r1-check.lean`
- `tasks/agent-loop/inbox/20261025-call-progress-obstruction-r1-verification.jsonl`
- `tasks/agent-loop/inbox/20261025-call-progress-obstruction-r1-review.md`
- `tasks/agent-loop/sprints/call-progress-obstruction-20261025-r1-outcome.md`

No other generated file, shared build output, untracked Force artifact or
repository-wide path is leased. Lean invocations remain serialized under r1's
four-invocation / one-process cap. P and Q may construct in parallel, but their
compiler invocations are scheduled serially by Luna.

