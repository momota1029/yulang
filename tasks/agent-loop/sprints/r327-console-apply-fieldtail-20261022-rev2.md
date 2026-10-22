# Sprint R327 — project exact operator members before dependent FieldTail selection

Revision 2 supersedes revision 1 only for the current source-to-result diagnosis and the newly leased projection integration seam. Revision 1 remains unchanged history.

Status: ACTIVE, solo serial lane. Baseline: pushed commit `483d26976`. Parent goal remains all unchanged Yulang2 playground samples through ordinary inference/execution, with implementation and source/native proofs.

## New evidence

An exact Console trace shows the top-level operator use at HIR occurrence 5 has both operands shaped `Int`, while its result row is still unshaped. The enclosing `say` application at occurrence 1 receives that same unshaped row. Therefore the current evidence does not show a broken Apply-to-FreshUse row map; the argument's result type is unresolved upstream. The provider's `int: Add` implementation member source is requested, but ordinary solver completion stops at `DeferredSelectionUnavailable` while the separate `say` Display FieldTail remains unresolved. `pinned_candidate_world` only adds an implementation member after `MissingMemberSource` escapes the solve call, so this path may never reach that projection branch.

## Next work

Inspect pre-selection `CandidateDeferredFieldTailReadbacks` on the exact Console module. Determine whether the top-level `Add` receiver has a unique, complete `Int` target before source selection. If so, use only that exact target identity and complete prerequisite evidence to project its implementation member before rerunning solve. Verify the selected `int.add` member graph fixes the operator result row to `Int`, then check that same row reaches the `say` FreshUse receiver and `Display.show`. Keep all ambiguity, unsupported inventory, incomplete prerequisite, and unstable frontier cases unavailable. If the pre-selection readback cannot authenticate the direct receiver, retain the original fail-closed behavior and trace the missing readback authority instead.

Contravariant `[io]` remains open `[io,'e]`; `[state]` is permitted. No narrowing or row closure may be introduced.

## Leases and verification

- Continue solo; no agents or background workers.
- Leases: `crates/yu-solver/src/candidate_scheme.rs`; `tools/inference-playground/src/lib.rs`; this contract, `notes/theory/2026-10-22-r327-console-apply-fieldtail.md`, and `tasks/agent-loop/current.json`.
- R327 cap remains 2400 seconds with no carryover. Commit and push coherent progress, inspect the outbound range, and never force-push.
- Run the exact unchanged Console CLI and focused selection/projection tests. Run the playground lib tests and check when the source projection change stabilizes.
- Console output, `int.add` projection, source/native adequacy, R149, all-samples completion, theorem closure, review, and production remain open.
