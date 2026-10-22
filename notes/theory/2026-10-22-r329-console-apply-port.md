# R329 — Console Apply-to-FreshUse port trace

## Starting evidence

R328 closed open at its 2400-second cap. The selected Int Add member result reaches the unchanged Console `say` Apply argument row. The imported `std::io::console.say` FreshUse preserves its exact `where 'a: Display` obligation and nested `value.show` FieldTail; the exact Display identity and same-FreshUse route checks pass.

The failure is later: the `say` Apply argument has positive Int evidence, while the corresponding imported FreshUse receiver readback has no positive shape. The unchanged Console CLI still returns `DeferredSelectionUnavailable`. See `notes/theory/2026-10-22-r328-console-result-row.md` for the exact route row evidence and reverted annotation experiment.

## R329 question

Trace the source Apply demand through its exact function ports and the imported `say` captured graph into the same FreshUse row used by `value.show`. Record the owner, occurrence, graph root, row mapping, and polarity at each step. Identify the first missing source-backed relation. Do not identify rows because both eventually have shape Int, and do not infer closed equality from the `[io]` annotation: contravariant `[io]` remains `[io,'e]` and admits `[state]`.

## Gates

Only change propagation after the source-to-candidate relation is established. Keep unsupported or ambiguous selection fail-closed. Run the focused Console trace after any implementation edit, then `cargo test -q -p yu-playground` at integration. The Console CLI must eventually print `hello from Yulang\n3\n` through ordinary inference and execution. All-sample execution, R149, source/native adequacy, theorem closure, independent review and production remain open.

## Result — Apply port recovered; selection remains open

The exact source constructor was the remaining port seam. Pinned `std::io::console.say` has a named formal `value`, an explicit unit result annotation, and `where 'a: Display`. `LocalSourceNamedGroup` retains the exact top-level `Definition` owner, first formal Lambda, and terminal body. The candidate schedule had applied the result annotation to the outer Lambda expression and used the definition root as its target. That placed `Unit` on the function-value path and left the terminal body without its declared result constraint.

For a top-level named group, the schedule now applies the source annotation to the exact `terminal_body` endpoint and targets that same body endpoint. It separately links the retained outer Lambda endpoint to the definition root. The path is guarded by the exact definition owner, unique named group, and first-formal Lambda identity. This preserves the source-derived curried function constructor, parameter ports, terminal result annotation, and body computation effect.

At the Console Apply occurrence, the existing `CandidateRelation::Apply` and `NativeInterface` retain the exact callee, argument, result, and effects. Its negative function demand contains the positive argument endpoint and negative result endpoint. The imported `say` graph's single FreshUse still maps its declared generic formal, `where` subject, and nested `value.show` receiver together. With the source-correct named-result construction, the selected Add result reaches the imported receiver as positive `Int`; this is now observed on the exact `show` FieldTail readback. No row was identified by matching shapes.

Selection remains fail-closed. The `show` readback has one exact `int.show` target match, complete implementation inventory, no unsupported targets, four positive bounds, zero exact negative bounds, and one reachable negative row edge. `negative_frontier_empty` is therefore false and `unique_candidate_field_tail_member` still returns `Unavailable`. A same-route join confirms receiver row 89 maps with retained `std::core::fmt::Display` subject row 90 in the same FreshUse. The active selection record contains two equal `Display` role identities, while the retained route graph exposes one corresponding where-source record. The duplication's owner and consumer are unresolved, so do not relax the frontier gate.

The Console CLI still returns `DeferredSelectionUnavailable`; expected output remains unobserved. The focused source/readback test now asserts that the Display receiver is `Int` before the pending selection. `cargo test -q -p yu-playground` passes all package groups (45 library tests, 23 CLI tests, plus remaining integration groups). Existing compiler warnings remain. This is implementation evidence only: R149, all samples, source/native adequacy, theorem closure, independent review, and production remain open.

The `[io]` effect annotation remains contravariant `[io,'e]`; a `[state]` argument remains admissible, with performed state in the residual. This change does not close an effect row or change the effect algebra.

## Next exact question

Trace why one source where-clause becomes two equal required-role identities, and join both entries plus the one negative row edge to every retained `where` subject and source-bound consumer. Establish whether the edge is exactly the authenticated Display prerequisite and whether the unique exact `int.show` target remains stable under it. Keep the selector fail-closed until this relation is source-qualified. Then continue the unchanged Console path through `show`, host writes, and execution.

## Scope and resources

Solo primary; no subagents. Exact held paths: `crates/yu-solver/src/candidate_scheme.rs`, `crates/yu-solver/src/candidate_source.rs`, `tools/inference-playground/src/lib.rs`, `tools/inference-playground/src/main.rs`, `tools/inference-playground/tests/cli.rs`, this contract, `notes/theory/2026-10-22-r329-console-apply-port.md`, `tasks/agent-loop/current.json`. `crates/yu-hir/src/module.rs` remains frozen as the completed R327 selected-root lookup fix.

Cap 2400 seconds, no carryover. Stop with an exact obstruction and tested receipt if no source-backed code slice remains.
