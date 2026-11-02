# R234 outcome — finite mandatory-record paper branch

Status: **REVIEWED PARTIAL**. Parent-premise delta **0**; roots **0/4**.
Baseline: `5deacdac4`; checkpoint: `0d31b1277` (pushed to `origin/yulang3`).

The checked Lean module formalizes the pinned paper's finite mandatory-field
relation, first-match lookup, directed child obligations, missing-label
rejection, and permutation conditions. It applies the relation to R233's
closed-tail width pair while preserving the fact that current `Sub` rejects
that pair. The independent source review was CLEAN for this bounded source
conformance claim. Primary pinned checking passed for all 22 declarations and
recorded their axiom sets in the proof handoff.

This does not define a Yulang source embedding, optional-field semantics,
recursive solver or callback execution; it does not reduce any original parent
premise, establish principality or termination, or prove Rust correspondence.
No Rust/Cargo/tests ran. The existing `.lake` grew by 437,434 bytes; no new
worktree, environment, target or cache path was created.

Exact artifacts: contract
`tasks/agent-loop/sprints/paper-record-width-r234.md`, module
`notes/theory/lean/YulangClosure/PaperRecordWidthR234.lean`, proof handoff
`tasks/agent-loop/inbox/paper-record-width-r234-proof.md`, and independent
review `tasks/agent-loop/inbox/paper-record-width-r234-review.md`.
