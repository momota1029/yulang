# R276 — identity-bound pinned role source inventory

Status: CHECKPOINTED_UNREVIEWED; solo primary implementation, no delegated workers.
Parent: unchanged Yulang2 Types/Console and broader playground sample goal under Authoritative R149.
Baseline: `779f32639` on `research/simple-sub-intrusion`.
Authority: R149 authentic `pair.say` resolution through the pinned `Display` role; exact `std::core::fmt` Git blob `fd7b6607094c9ad70bde1fd41890363fa8bd6b31`; parser-owned role/impl node positions.

## Outcome and evidence

Build an app-local pinned role-source inventory for exact bundled modules that retains the source path, Git blob identity, `ModuleIdentity`, parser snapshot, syntax diagnostics count, and parser-owned role/impl node positions. Use the inventory to prove that parser nodes anchor the exact pinned `std::core::fmt` `Display` role and two-element tuple implementation, and that the authenticated bundled bytes contain their complete declarations. Keep role selection and method meaning unresolved; this step provides authenticated source input for the next resolver step.

## Evidence adjustment

The pinned `fmt.yu` currently produces syntax diagnostics in this parser, so `ShadowArtifact::from_parsed` correctly refuses to publish a HIR artifact. R276 does not mask those diagnostics or claim full declaration ranges as parser-owned. It retains the exact `ParsedFile`, counts diagnostics, retains only the available parser node anchors, and checks complete role/implementation text against the independently blob-verified bundled source. Future semantic use must first resolve this parser compatibility boundary.

Falsifiers: a changed blob/path/module identity is accepted; a role/impl position comes from another parsed module; tuple arity is inferred from display text rather than parser-owned syntax; any implementation is selected or executed by spelling alone.

## Exact write paths

- `tools/inference-playground/src/pinned_stdlib.rs`
- `tools/inference-playground/src/lib.rs`
- this contract
- `notes/theory/2026-10-21-r276-pinned-role-source-inventory.md`
- `tasks/agent-loop/inbox/20261021-r276-pinned-role-source-inventory.md`
- primary-owned `tasks/agent-loop/current.json`
- `tasks/current.md`

No method/role solving, imported HIR linking, type inference, runtime, sample output, proof closure or production promotion. The unchanged examples and parent proof gates remain OPEN.

## Method, verification and limit

Parse exact sources with their bundled byte identity and an environment carrying the exact imported operator header. Keep each parser snapshot paired with its `ModuleIdentity`; expose parser-owned role/impl node anchors without converting them into semantic role IDs. Verify complete declarations against the exact pinned bytes. Focused inventory test for the pinned `fmt.yu`, `cargo check -p yu-playground`, sprint static check and `git diff --check`. One heavy Cargo process; no independent review under user-directed solo work.

Budget: 600 seconds, no carryover. The next decisive owner is generic role/method selection over this authenticated source inventory.
