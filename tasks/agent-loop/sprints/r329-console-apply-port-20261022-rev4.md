# Sprint R329 — Console Apply-to-FreshUse port trace

Revision 4 records the stability audit. Revision 3 remains immutable history.

## Result

The stability audit inspected the row-pair matcher and same-FreshUse admission in `crates/yu-solver/src/candidate_scheme.rs`, plus live frontier readback and bound insertion/replay in `crates/yu-solver/src/lib.rs`.

The source-authenticated pair remains two distinct rows. The captured graph carries reciprocal bounds and validates the Display/FieldTail pairing in one FreshUse. That proves provenance and transport of the relation, but does not prove equality or that later source-bound consumers cannot add constraints to either endpoint. Live receiver readback recomputes its lower frontier and counts the negative upper edge. The value-task path can add bounds and replay exact endpoints; no frozen-frontier or consumer-closure receipt was found.

No safe selector or propagation edit follows. Keep `negative_frontier_empty` strict. The next proof step must close all consumers of both rows before dispatch, or derive a representation that checks the Display prerequisite against the exact substituted subject without interpreting the one-way live upper edge as equality. Details and inspected locators are in `notes/theory/2026-10-22-r329-console-apply-port.md`.

## Open gates

Console output `hello from Yulang\n3\n`, all remaining samples, R149, source/native adequacy, theorem closure, independent review and production remain open. The `[io]` contravariant annotation remains `[io,'e]`, admitting `[state]` and retaining performed state in the residual. Solo scope; no subagents or independent review lane.

## Resources

Cap 2400 seconds, no carryover. Charged time is 2100 seconds. Do not reuse the remaining sprint budget for a speculative selector relaxation; resume with the exact source/native stability obligation above.
