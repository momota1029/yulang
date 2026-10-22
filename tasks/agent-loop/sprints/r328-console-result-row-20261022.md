# Sprint R328 — Console operator result-row correspondence

Continuation of the persistent Yulang2 playground goal. Baseline is the current worktree atop pushed commit `483d26976`; R327 work remains uncommitted because `.git` is read-only in this sandbox. R327 exhausted its 2400-second cap; this sprint starts with no carryover.

## Objective

Trace the exact result row of `1 + 2` through the pinned imported operator provider, selected `int.add` member graph, and `say` Apply/FreshUse. Explain why Int operands and an `int -> int -> int` selected member do not yield a positive Int shape at the operator result. Prove the source/candidate row correspondence or produce a minimal counterexample, then repair only the evidenced propagation rule and retain fail-closed selection.

The overall objective remains every unchanged Yulang2 playground sample through ordinary inference and execution, plus implementation and proof closure. Console output, R149, source/native adequacy, all-sample completion, and theorem closure remain open.

## Evidence at entry

- R327 pre-selection readbacks authenticate a unique, complete Int Add target. Exact source member projection discharges the Int Add FieldTail.
- The exact Console trace links the `say` Apply argument to the `1 + 2` result row; both operands are Int, the operator result row is unshaped, and the dependent Display receiver remains unshaped.
- Selected-member prelude-role retention now restricts import lookup to selected source roots. The former unrelated recovered `text` export failure is fixed.
- Playground lib tests pass 45/45; `cargo check -q -p yu-playground` passes; Console CLI still returns `DeferredSelectionUnavailable`.
- Contravariant `[io]` means open `[io,'e]`; `[state]` is permitted.

## Work and verification

- Solo serial lane; do not spawn agents or background workers.
- Leases: `tools/inference-playground/src/lib.rs`, `crates/yu-solver/src/candidate_scheme.rs`, `crates/yu-solver/src/candidate_source.rs`, `crates/yu-solver/src/candidate_value_graph.rs`, this contract, the R328 note, and current sprint state. Add an exact lease revision before editing another source file.
- Run the Console projection test, full `cargo test -p yu-playground`, exact `--run-module` CLI, `cargo check -p yu-playground`, and repository-level tests as relevant. Run sprint consistency checks and `git diff --check`.
- Cap 2400 seconds, no carryover. Keep user informed and make coherent commits/pushes when the environment permits. Never force-push.
