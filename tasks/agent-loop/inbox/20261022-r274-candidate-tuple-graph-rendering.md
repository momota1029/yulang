# R274 primary handoff — candidate Tuple graph rendering

Contract: `tasks/agent-loop/sprints/candidate-tuple-graph-rendering-20261022-r274-rev1.md` (revision 1; initial contract frozen).
Baseline: `81ba87d7f` plus the in-progress R274 renderer diff.
Status: implementation result; experimental and unreviewed. Revision 1 adds the F5 Tuple view exhaustiveness fix required to compile the playground package.

Parent: unchanged Yulang2 samples plus proof-backed inference/evaluation. The candidate graph exposes ordered Tuple children, but playground rendering previously descended only through Function children. This packet adds nested ordered Tuple display to that same candidate graph output.

This is not a closed public scheme, Types pane, source/native proof or sample-success claim. Exact scope is `render.rs`, focused `lib.rs` tests, `yu-solver/src/lib.rs` legacy view compatibility, this contract, note, inbox and current state. F5 tuple scheme reconstruction remains explicitly unavailable.

Outcome class: provisional implementation.

Implementation: renderer interns Tuple children in iterator order and prints a distinct `Tuple([n...])` constructor. Direct and nested Tuple regression passed. The F5 adapter traverses positive and negative Tuple children, then returns `SolveAvailabilityError::IdentityExhausted` at unsupported reconstruction; it does not flatten or fabricate a term. `root_value_for` reports Tuple as `SolvedValue::Unknown`.

Checks: `cargo test -p yu-playground --lib candidate_graph_renderer_exposes_nested_tuple_children_in_order -- --nocapture` passed (1 test; package compiled); `git diff --check` passed. Existing `yu-hir` / `yu-solver` warnings were observed, with no active-diff warning identified. No independent review under the user's solo-work instruction.

Parent application: candidate graph output exposes ordered Tuple children only. R149 Types/Console, Yulang2 sample execution, F5 Tuple reconstruction, source/native correspondence, A/B proof and production remain OPEN. No sample or theorem claim follows.

Changed paths: `tools/inference-playground/src/render.rs`, `tools/inference-playground/src/lib.rs`, `crates/yu-solver/src/lib.rs`, revision 1 contract, theory note, inbox and current state. Writer: `/root`; writes stopped after checkpoint preparation. Commit/push pending primary integration.
