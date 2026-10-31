# R104 v2 admission

Admitted by Luna under the standing Rust/Lean goal after the R104 fresh Rust
pre-execution review rejected the frozen Stage-1 candidate. This version is an
exact, bounded amendment; R104 r1 and its failure receipt remain byte-preserved.

Amendment: `tasks/agent-loop/sprints/effect-permission-source-causality-20261101-r104-v2.md`.
Base contract: `tasks/agent-loop/sprints/effect-permission-source-causality-20261101-r104.md`.

The amendment preserves all four existing Rust source leases, source semantics,
assertions, two remaining Cargo calls, timeout/RSS/CPU/tmpfs limits, and the
4,200-second aggregate envelope. It adds the exact `--show-output` harness flag
and requires repairs for the rejected no-row trace and fresh-use Support
crosswalk. No call is permitted before a fresh complete-component review.

The one Lean call and independent receipt review passed. Its artifacts are
eligible for a standalone reviewed checkpoint, with parent/source/native
obligations still open. This admission does not promote Rust source or close the
goal.
