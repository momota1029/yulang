# R274 primary handoff — candidate Tuple graph rendering

Contract: `tasks/agent-loop/sprints/candidate-tuple-graph-rendering-20261022-r274.md`.
Baseline: `a5744c060`.
Status: primary implementation in progress; experimental and unreviewed.

Parent: unchanged Yulang2 samples plus proof-backed inference/evaluation. The candidate graph exposes ordered Tuple children, but playground rendering currently descends only through Function children. This packet adds nested ordered Tuple display to that same candidate graph output.

This is not a closed public scheme, Types pane, source/native proof or sample-success claim. Exact scope is `render.rs`, its focused `lib.rs` tests, this contract, note, inbox and current state.

Checks: focused playground renderer tests, static sprint consistency and `git diff --check`; one Cargo process maximum. No independent review under the user's solo-work instruction.
