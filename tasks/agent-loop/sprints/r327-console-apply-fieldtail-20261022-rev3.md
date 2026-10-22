# Sprint R327 — exact operator member projection and result-row trace

Revision 3 supersedes revision 2 only for the admitted pre-selection Add-member projection and the resulting unresolved result-row premise. Revisions 1 and 2 remain unchanged history.

Status: ACTIVE, solo serial lane. Baseline: pushed commit `483d26976`. Parent goal remains all unchanged Yulang2 playground samples through ordinary inference/execution, with implementation and source/native proofs.

## Established in this revision

- Pre-selection readbacks authenticate the `Int` Add receiver: unique `int` target, complete inventory, no unsupported targets, stable positive frontier, empty negative frontier, and no prerequisites.
- The playground now projects exact Add implementation members by authenticated role and implementation source identity only when those readback gates hold.
- After projection, the Int Add FieldTail is discharged. The selected `int.add` body delegates to pinned `std::int::add`, whose source type is `int -> int -> int`.
- The top-level operator result remains unshaped, so the dependent `say` Apply/FreshUse Display receiver remains unshaped and inference returns `DeferredSelectionUnavailable`.

## Next work

Trace the selected `int.add` member's function result constraints through its imported `std::int::add` call, the exact operator graph result row, and the `say` FreshUse receiver. Establish polarity and source-owner lineage with a focused counterexample or invariant. Do not invent equality between rows or infer shape from unrelated evidence. Keep unresolved/ambiguous FieldTails unavailable.

The user's effect-row correction remains binding: contravariant `[io]` means open `[io,'e]`, allowing `[state]`; no row closure or narrowing is authorized.

## Leases and verification

- Continue solo; no agents or background workers.
- Exact leases: `tools/inference-playground/src/lib.rs`, this contract, `notes/theory/2026-10-22-r327-console-apply-fieldtail.md`, and `tasks/agent-loop/current.json`. `candidate_scheme.rs` is released unchanged.
- R327 cap remains 2400 seconds with no carryover. Commit and push coherent progress, inspect the outbound range, and never force-push.
- Run the focused Console projection test, exact unchanged Console CLI, playground library tests and check as the integration stabilizes, `git diff --check`, and sprint static consistency checks.
- Current verification: focused Console projection test passes; `cargo check -q -p yu-playground` passes with existing warnings; exact CLI remains `DeferredSelectionUnavailable`. Full playground lib tests report 41 passed and 4 Types sample failures (candidate deferred selection or selected source-import resolution); those failures remain untraced.
- Console output, Display selection, source/native adequacy, R149, all-samples completion, theorem closure, review, and production remain open.
