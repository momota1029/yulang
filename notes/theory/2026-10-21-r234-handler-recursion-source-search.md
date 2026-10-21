# R234 — Handler and recursion source schedule search

## Question and scope

Starting from the accepted R221 recursive callback fixture, do ordinary shallow handlers around recursive, helper, callback, or provider calls produce an effect item alias owned by a third row and consumed by a later `Work::Bound`? A fifth variant puts the operation-producing handler directly in the recursive loop body.

The probe is test-only in `crates/yu-solver/src/shadow_apply/local_source_observation.rs`. It parses and lowers each source, runs candidate inference, rejects conflicts, requires a complete forest event log, checks each effect parent write against its ordered row-merge trace, then follows effect-row representatives in event order before each WorkBound. A hit requires an already-aliased raw item and an owner outside that item's equivalence class.

## Result

All five source variants were candidate-accepted. The direct recursive call, helper call, callback call, and provider call each produced two traced effect-row merges and three WorkBound events. The handler in the recursive loop body produced no effect-row merges and no WorkBounds. None produced a hit.

In the four call-placement cases, the observed WorkBound raw effect keys retained distinct owner and item representatives at the point of consumption. For example, the direct case consumed `(owner EffectRow(13), item EffectRow(32))` and `(owner EffectRow(24), item EffectRow(34))`; the two merges were `Effect(39)->Effect(16)` and `Effect(40)->Effect(38)`. The other three variants had the same event shape with source-local IDs. The recursive-body case contributed no WorkBound observation.

## Conclusion and limits

This closes only the finite R234 source-family search. These placements did not supply the needed third-owner alias followed by a WorkBound. It does not prove that handlers cannot create such a schedule, and it does not close R71, R72, or the parent computation-forwarding theorem. No production implementation change is justified by this result.

## Checks

- Focused `r234_handler_recursion_source_schedule_variants`: passed; 1 test.
- `cargo test -p yu-playground`: passed, including unit and integration test suites.
- Sprint static check, tooling unit tests, and `git diff --check`: recorded in the R234 contract/current state.
- Independent review: not run; solo primary search.
