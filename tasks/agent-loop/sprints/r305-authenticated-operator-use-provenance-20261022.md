# Sprint R305 — authenticated operator-use provenance

Status: OPEN_CONTINUATION, solo Luna primary, no independent review; parent R149 remains OPEN.
Baseline: `3ece25edf1ab84fd543c4e311b890a70f97c60d5` on `research/simple-sub-intrusion`.
Parent: unchanged 142-byte Types and 92-byte Console samples and their original source/native obligations. No sample rewrite or operator semantic change is authorized.

## Outcome

Preserve the exact provenance selected for a dynamic operator use from the immutable full-parse operator table into HIR. For each retained `HirOperator`, evidence must identify the exact use occurrence and fixity, whether the selected declaration is local or imported, and for imported declarations the exact syntax-dependency slot, module label/revision, and declaration source range. The use source and declaration provenance must remain distinguishable. This packet stops before resolving the operator declaration's value binding, lowering operator applications into candidate constraints, or assigning method meaning.

This narrows the missing premise observed in the pinned `Display.say` source: its `+` use is accepted using the `lib/std/core/ops.yu` syntax dependency, but current HIR retains only spelling/fixity/range. A source/native-safe future candidate path needs this chosen origin before it can connect the operator declaration to its original value source. No rewrite from `+` to `.add` is allowed.

## Required source correspondence and falsifiers

Trace the pinned `Display.say` `+` token from its exact consumer parse node through the accepted operator fixity site and selected syntax dependency provenance into HIR. The test must assert the spelling/fixity/use source identity, imported dependency slot, module label, revision, and exact provider declaration range against the pinned `core/ops.yu` source. A local operator declaration must remain Local even when its spelling matches an imported operator; a foreign dependency slot, wrong fixity, stale range, recovered source or same-spelled shadow declaration must not be attributed to the pinned declaration.

The implementation may expose provenance through a small read-only API, but may not reparse or reconstruct operator meaning, resolve a value binding by spelling, or change binding powers, fixity merging, associativity, evaluation, or diagnostics. If the current immutable table cannot retain enough identity to satisfy the contract without an unsafe inference, record the exact missing source owner and stop this packet at that counterexample.

Evidence target: focused `yu-syntax` provenance tests, focused HIR association test, pinned `Display.say` provenance regression, `cargo check -p yu-hir --features shadow`, `cargo check -p yu-playground`, and the unchanged Types boundary test. Tests are implementation/source evidence, not theorem closure or independent review.

## Observed counterexample and partial result

The additive `OperatorDeclarationProvenance` / `OperatorUseProvenance` API exposes the chosen origin, declaration range and imported dependency record. HIR retains this receipt on each `HirOperator`. Positive controls pass for a local infix declaration and an imported infix declaration; the imported HIR test checks slot, provider range, module label and revision.

The exact pinned source falsifies the original end-to-end target before HIR association. For `lib/std/core/fmt.yu`, `HeaderInfo` currently retains only the explicit `std::num::frac::frac` import and drops the three preceding glob imports, including `use std::core::ops::*`. The selected syntax environment therefore has no `lib/std/core/ops.yu` dependency; the `+` inside the original `Display.say` remains a token directly under the root CST and has no `HirOperator` occurrence to receive provenance. A query of table provenance by spelling would not authenticate that source occurrence. The exact next source owner is the header import/use-declaration projection that loses glob routes; it was not in R305's lease, so R305 stops here without weakening the contract.

## Proof correspondence and parent application

The proof note traces one original source operator occurrence to one immutable table site and one imported syntax dependency receipt. It establishes only provenance preservation. It does not establish that the declaration source is an exported value, that its value has a candidate scheme, that a receiver is ready, or that the result is principal or executable. The design's identity/payload contract requires preserving source identity separately from later candidate endpoints; the proof companion's Capture replacement theorem still requires its full dependency and observation boundary. The effect correction remains in force: contravariant `[io]` abbreviates `[io,'e]`, so `[state]` alone is not a violation.

The positive-control receipt API preserves operator provenance whenever an actual `HirOperator` exists. It does not yet provide a receipt for the original `Display.say` use because the pinned source's glob imports are absent from the syntax environment. The next exact boundary must retain that imported module route and then recheck the original operator occurrence. Operator value ownership, member candidate formation, unchanged Types/Console execution and every original proof gate remain OPEN.

## Exact leases

`crates/yu-syntax/src/operator_table.rs`, `crates/yu-syntax/src/syntax_environment.rs`, `crates/yu-syntax/src/full_parse.rs`, `crates/yu-hir/src/lib.rs`, `tools/inference-playground/src/pinned_stdlib.rs`, `tools/inference-playground/src/lib.rs`, this contract, `notes/theory/2026-10-22-r305-authenticated-operator-use-provenance.md`, and Luna-owned `tasks/agent-loop/current.json`.

No edits to `yu-solver`, source export resolution, role/member candidate schemes, runtime semantics or the pinned stdlib bytes are authorized in this packet. One serial primary process, 2400-second cap, no carryover, no background work or subagents. Preserve all UNKNOWN legacy worker leases. Luna alone integrates and pushes. End the session with the primary WAITING only after writes and processes stop.

## Lanes, resources, and review

Solo degraded serial execution: Luna owns both the bounded HIR implementation and constructive source-to-HIR provenance argument. No independent reviewer is available under the explicit solo constraint; the result remains unreviewed. Use no parallel cargo process. Stop if operator site provenance cannot be matched to the exact source dependency without expanding into declaration-value resolution; that is a new boundary.

## Remaining parent work

Operator declaration value identity and source carrier; member candidate root/scheme and receiver prerequisite; tuple `show` body projection; settled selection and body typing; unchanged Types and Console execution; full Tuple publication/runtime; source/native proof, original A/B claims, independent review, principality, termination and production remain OPEN. R149 remains OPEN.
