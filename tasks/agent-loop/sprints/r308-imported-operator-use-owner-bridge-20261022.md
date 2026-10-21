# Sprint R308 — imported operator use to exact provider source owner

Status: READY, solo Luna primary, unreviewed; parent R149 remains OPEN.
Baseline: `76cb4ea7a` on `research/simple-sub-intrusion`.
Parent: unchanged Yulang2 Types and Console source and original source/native obligations.

## Outcome

Carry the exact provider declaration/body identity from R307 through the consumer's selected imported syntax dependency to an already-associated imported `HirOperator`. The `Display.say` `+` must resolve only when its imported dependency label/revision, declaration range, spelling and fixity identify exactly one nonrecovered source-owned operator in the supplied provider indexes. The provider RHS must remain the original `\\x -> \\y -> x.add y`.

This is an occurrence-to-provider source bridge only. Keep the consumer use and provider declaration/body keys distinct. Do not lower the RHS into a candidate, interpret `+` as `.add`, type/select a member, change operator semantics or add runtime behavior.

## Evidence and falsifiers

- `SemanticImports` retains operator source owners only from provider indexes matching the consumer parse's selected `SyntaxDependencyProvenance` label and revision.
- Lookup consumes the selected imported operator receipt and requires exact declaration range, spelling and fixity; no same-spelling fallback is permitted.
- Exact pinned `Display.say` `+` resolves to provider body text/range from `lib/std/core/ops.yu` at the dependency's pinned revision.
- Wrong/unavailable provider revision, module label, declaration range, spelling/fixity, ambiguity or recovered owner fails closed. Local operator provenance does not fabricate an imported provider.
- Run source-owner and pinned fmt regressions, `cargo check -p yu-hir --features shadow`, `cargo check -p yu-playground`, and unchanged Types/Console boundaries as available. Passing checks establish source implementation evidence only.

## Proof correspondence and boundary

The unified design §§4.1–4.5 keeps source identity distinct from current solver endpoints and semantic payload; operator ownership cannot become a selected value by spelling. Method selection remains after relevant bounds settle. The proof companion §§3–4 and §§7–8 separates source correspondence from Capture/FreshUse and whole compiler theorems. The effect correction remains in force: contravariant `[io]` means `[io,'e]`, so passing `[state]` alone is not a violation.

R307 remains unreviewed. R308 adds no source typing, candidate scheme, member obligation, solver propagation, unchanged sample execution, theorem closure or production authority. R149 and all proof/production gates remain OPEN.

## Exact leases and resources

`crates/yu-hir/src/module/source_exports.rs`, `crates/yu-hir/src/module.rs`, `tools/inference-playground/src/lib.rs`, this contract, `notes/theory/2026-10-22-r308-imported-operator-use-owner-bridge.md`, and Luna-owned `tasks/agent-loop/current.json`.

One serial primary process, 1200-second cap, no carryover, no background work or subagents. No callable next-action dispatcher is available in this session; selection is Luna's solo continuation from R307's recorded next boundary. Preserve all UNKNOWN legacy worker leases. No `yu-syntax`, `yu-solver`, runtime, pinned-byte or semantics changes. No independent reviewer is assigned under the explicit solo constraint; evidence stays unreviewed.
