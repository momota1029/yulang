# Sprint R329 — Console Apply-to-FreshUse port trace

## Parent and scope

The parent objective remains all unchanged Yulang2 playground samples working through ordinary inference and execution, with source/native proof. Preserve the source and native quantifiers and all design/proof gates. R149, source/native adequacy, theorem closure and production remain open. Contravariant `[io]` means `[io,'e]`, admits `[state]`, and leaves performed state in the residual.

## Starting evidence

R328 ended open at its 2400-second cap with no carryover. The selected Int Add member result reaches the unchanged Console `say` Apply argument row. The imported `std::io::console.say` FreshUse carries the exact `where 'a: Display` obligation and nested `value.show` FieldTail together. The exact `std::core::fmt::Display` identity matches, and both same-FreshUse route checks pass.

The `say` Apply argument has positive Int evidence, while the corresponding imported FreshUse receiver readback has no positive shape. The unchanged Console CLI still returns `DeferredSelectionUnavailable`. The exact route trace and the reverted return-annotation experiment are recorded in `notes/theory/2026-10-22-r328-console-result-row.md`.

## R329 question

Trace the source Apply demand through its exact function ports and the imported `say` captured graph into the same FreshUse row used by `value.show`. Record the owner, occurrence, graph root, row mapping, and polarity at each step. Identify the first missing source-backed relation. Do not identify rows because both eventually have shape Int, and do not infer closed equality from the `[io]` annotation.

## Success evidence and gates

Establish a constructive source-to-candidate correspondence before changing propagation. Keep unsupported or ambiguous selection fail-closed. Run the focused Console trace after any implementation edit, then `cargo test -q -p yu-playground` at integration. The Console CLI must eventually print `hello from Yulang\n3\n` through ordinary inference and execution. All-sample execution, R149, source/native adequacy, theorem closure, independent review and production remain open.

## Scope, leases, and resources

Solo primary; no subagents. Held paths: `crates/yu-solver/src/candidate_scheme.rs`, `crates/yu-solver/src/candidate_source.rs`, `tools/inference-playground/src/lib.rs`, `tools/inference-playground/src/main.rs`, `tools/inference-playground/tests/cli.rs`, this contract, `notes/theory/2026-10-22-r329-console-apply-port.md`, and `tasks/agent-loop/current.json`. `crates/yu-hir/src/module.rs` remains frozen as the completed R327 selected-root lookup fix.

Cap: 2400 seconds, no carryover. Stop with an exact obstruction and tested receipt if no source-backed code slice remains.
