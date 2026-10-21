# R231 — Search accepted source schedules for cross-owner WorkBound

Status: CLOSED_SOURCE_NATIVE_EVIDENCE; Luna solo primary, no independent review.
Branch / baseline: `research/simple-sub-intrusion` / `71cda7951`.
Parent: unchanged computation-forwarding theorem §§1, 6–7; R71/R72 remain OPEN.

## Fixed outcome

Use the exact accepted R221 callback/loop fixture as a source seed and test a small family of ordinary source-level call-placement variants. Determine whether any variant produces an owner-qualified third-owner item merge followed by a later production `Work::Bound` selecting that raw slot. For every hit, join source physical slot/admission, ordered alias history, later WorkBound raw key and source occurrence. For misses, identify which source transition or consumer owner remains absent; do not turn a bounded search into a general impossibility claim.

## Exact lease and boundaries

- `crates/yu-solver/src/shadow_apply/local_source_observation.rs` — `#[cfg(test)]` source observer/search only.
- `tasks/agent-loop/sprints/cross-owner-source-schedule-search-20261021-r231.md`
- `notes/theory/2026-10-21-r231-cross-owner-source-schedule-search.md`
- `tasks/agent-loop/current.json`

No production code, source sample, semantics, expected output, theorem quantifier or test acceptance rule changes. No subagents. All six tested variants parsed/lowered and solved without errors or conflicts. The complete ordered forest and WorkBound trace contained no cross-owner post-alias hit. This is a bounded negative result, not a general impossibility claim. Use it to choose the next proof method.

## Success/falsification

Success is a concrete accepted source whose exact third-owner slot's item is aliased by an ordered parent write and whose later production WorkBound event selects that same raw slot, with exact source owner and retained fiber lineage. A falsifier for any claimed hit is a source mismatch, equal row without physical slot, WorkBound before the merge, owner in the merged class, or missing exact retained fiber. A search miss establishes only that none of the tested variants provides the witness.

## Checks and resources

The focused test `r231_cross_owner_source_schedule_variants`, `cargo test -p yu-playground`, sprint static check, all 57 sprint tooling tests, and `git diff --check` passed. Budget cap 720 seconds, no carryover. Runtime was not precisely metered, so the full cap is charged conservatively. No production implementation is authorized by this search.
