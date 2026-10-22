# Sprint R328 — Console result row and package regressions

Revision 3 supersedes rev2 after package integration failures were repaired and the Add-to-Apply row trace produced new evidence. Earlier revisions remain immutable history.

## Parent and scope

The parent objective remains all unchanged Yulang2 playground samples working through ordinary inference/execution, with implementation and source/native proof. R149, source/native adequacy, theorem closure and production remain open. Preserve the approved contravariant `[io]` interpretation as `[io,'e]`, which admits `[state]` and keeps state in the residual when it is performed.

## Evidence completed

- Exact Int Add FieldTail selection reads back and projects the pinned `int.add` member only with complete, stable positive-frontier evidence. Its output row becomes Int after the selected member relation is admitted.
- The selected operator result row and the `say` Apply argument are the same live row in the exact Console trace; after Add selection both read back as Int. This closes the specific Add-result-to-Apply-argument transport question.
- The deferred `Display.show` receiver remains a different row, with no positive concrete bound; the observed pair has only reciprocal upper-row edges. The source/use map connecting this nested obligation to the imported `console.say` FreshUse is not yet established. Do not equate it to the Apply argument by shape alone.
- A minimal generic local definition calling a deferred FieldTail receives Int at that FieldTail through ordinary Apply. This rules out a general failure of generic-definition FreshUse or Apply argument propagation; the remaining obstruction is specific to the pinned imported `say` route/role obligation.
- Added a regression for generic FieldTail FreshUse and fixed retained-map accounting: `RetainedFreshUseMaps::bytes` now counts `source_field_tail_obligation_rows`. The focused regression passes.
- The full `cargo test -q -p yu-playground` passes all groups, including 45 library tests and 23 CLI tests.
- Absolute source file identity normalization fixed the CLI structural-projection failures; `--intrusion` conditional conflicts still withhold observations.

## Next exact question

Trace the imported `std::io::console::say` definition and its `where 'a: Display` obligation through its source owner, captured graph, exact FreshUse map and Apply argument. Identify why the nested `value.show` receiver is not connected to the same invocation's concrete argument. Keep the source owner, occurrence, four ports and polarity throughout. Establish the source-to-candidate correspondence before changing propagation; do not add an equality based only on both rows eventually looking like Int.

## Leases

Primary `/root`, solo; no subagents. Held paths: `crates/yu-solver/src/candidate_scheme.rs`, `crates/yu-solver/src/candidate_source.rs`, `tools/inference-playground/src/lib.rs`, `tools/inference-playground/src/main.rs`, `tools/inference-playground/tests/cli.rs`, this contract, `notes/theory/2026-10-22-r328-console-result-row.md`, and `tasks/agent-loop/current.json`. `crates/yu-hir/src/module.rs` remains frozen as the completed R327 selected-root lookup fix.

## Gate and convergence

The unchanged Console CLI must still reach `hello from Yulang\n3\n` through ordinary inference and execution. Current `DeferredSelectionUnavailable` means this gate is open. Keep all unsupported, ambiguous or unstable source selection fail-closed. Source/native proof, every other Yulang2 sample, A/B parent obligations, independent review and production remain open. Use focused checks for the imported `say` route, then rerun the package suite after the integration change. Record the exact source identity, rows, polarity and remaining premise in the note.

## Resource receipt

R328 cap: 2400 seconds, no carryover. Charged at revision: 1368 seconds. Current worker is the solo primary; prior CLI test failure diagnosis and repair are included in this sprint, not a separate worker lane.
