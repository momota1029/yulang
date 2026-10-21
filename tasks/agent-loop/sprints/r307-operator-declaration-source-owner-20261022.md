# Sprint R307 — authenticated operator declaration source owner

Status: READY, solo Luna primary, unreviewed; parent R149 remains OPEN.
Baseline: `4588437212adf135bc74874aaba58c562aafb0c4` on `research/simple-sub-intrusion`.
Parent: unchanged Yulang2 Types and Console source and original source/native obligations.

## Outcome

Resolve the imported operator declaration receipt from R305/R306 to one exact parse-owned source declaration and its original value-body source range. For the unchanged pinned `Display.say` `+`, map the imported `lib/std/core/ops.yu` label/revision/declaration range to the exact local `OperatorHeader`, its public Infix `+` metadata, and the original RHS source `\\x -> \\y -> x.add y`. The use occurrence and provider declaration/body remain distinct identities.

This is source ownership only. Do not create a value by spelling lookup, rewrite `+` to `.add`, admit a candidate scheme, select a method, or change operator meaning. A source owner may be exposed as a read-only identity record derived from the exact pinned parse.

## Required evidence and falsifiers

- Provider lookup accepts the exact module identity/revision and declaration range from the HIR operator receipt, then returns a parse-owned operator source identity with its precise `SourceNodeKey`, visibility, spelling, fixity and RHS range.
- The provider bytes at that range match the pinned public `infix (+)` declaration and original lambda body. A same-spelled local declaration, different fixity, stale revision, wrong range, duplicate/ambiguous declaration, or recovered header/body must not resolve.
- Re-exported or imported syntax provenance must remain separate from value-export routes; no operator value resolution by spelling is inferred.
- Run focused source-owner tests, pinned fmt/operator trace, `cargo check -p yu-hir --features shadow`, `cargo check -p yu-playground`, and unchanged Types boundary. Tests establish implementation/source evidence only.

## Proof correspondence and boundary

Trace the original consumer operator use range and imported syntax dependency to one pinned provider parse, then to one header node and body byte range. Preserve use/source identity, provider declaration identity and current solver endpoints as separate objects. This establishes only a source-to-source correspondence. The unified design requires original identity to remain distinct from current endpoints and semantic payload; the proof companion's Capture replacement still requires full dependency closure and joint observation. The effect correction remains in force: contravariant `[io]` means `[io,'e]`, so `[state]` alone is not an effect violation.

The value's candidate scheme, receiver/member relation, deferred readiness, body typing, unchanged Types/Console execution, full Tuple support, source/native proof, A/B, principality, termination, review and production remain OPEN. R149 remains OPEN.

## Exact leases and resources

`crates/yu-hir/src/module/source_exports.rs`, `crates/yu-hir/src/module.rs`, `tools/inference-playground/src/lib.rs`, this contract, `notes/theory/2026-10-22-r307-operator-declaration-source-owner.md`, and Luna-owned `tasks/agent-loop/current.json`.

One serial primary process, 1800-second cap, no carryover, no background work or subagents. Preserve UNKNOWN legacy worker leases. No `yu-solver`, syntax, parser, runtime, pinned-byte or member-selection edits. No independent reviewer is assigned under the explicit solo constraint; evidence remains unreviewed. Stop before constructing candidate semantics if exact declaration ownership cannot be established.
