# R275 rev1 — preserve FieldTail and fail closed before role resolution

Revision reason: the first downstream `yu-playground` package check found one exhaustive solver consumer of `LocalSourceForm`. Add that owner to complete compile integration. The initial R275 contract remains immutable.

Status: ACTIVE; solo primary implementation, no delegated workers.
Parent: unchanged Yulang2 Types/Console and broader playground sample goal, under Authoritative `notes/design/2026-10-20-r149-types-console.md`.
Baseline: `264fd5c38` plus the in-progress FieldTail source-carrier change.
Authority: R149 authentic `pair.say` Display role resolution; existing Y3 `PendingFieldTailSource` and association bridge in `crates/yu-hir/src/shadow.rs`; existing ordinary local-source carrier conventions.

## Outcome and evidence

The exact Types binding prefix infers, while the final unchanged `pair.say` fails `unsupported source`; as a binding, `my displayed = pair.say` fails HIR `StructuralProjection`. Extend ordinary local source to retain each FieldTail's receiver, member spelling, member range and tail source identity. Extend the candidate source traversal to visit the receiver, but explicitly return unavailable at FieldTail construction until authentic method-role resolution exists. Never invent a type constraint from a member spelling.

Focused HIR tests cover the exact Types source and chained `base.first.second`, asserting the member tokens and receiver order. The `yu-playground` crate must compile. R275 does not claim the exact program now infers or runs.

Falsifiers: receiver order/identity is lost; a member is reconstructed from rendered text; malformed/recovered tails are admitted; the candidate solver fabricates a member type or accepts the exact program without role evidence.

## Exact write paths

- `crates/yu-hir/src/module/local_source.rs`
- `crates/yu-solver/src/candidate_source.rs`
- this revision contract
- `notes/theory/2026-10-21-r275-field-tail-source-carrier.md`
- `tasks/agent-loop/inbox/20261021-r275-field-tail-source-carrier.md`
- primary-owned `tasks/agent-loop/current.json`
- `tasks/current.md`

No role selection, imported module linking, public type export, runtime behavior, sample output, theorem closure or production promotion. Keep exact R149 source unchanged. Continue the same broader goal after this prerequisite; this is not a reduced completion target.

## Verification and limit

Focused HIR tests, `cargo check -p yu-playground`, an exact-sample CLI probe confirming the role consumer still fails closed, `python3 tools/agent_sprint.py check`, and `git diff --check`. One heavy Cargo process, no independent review under the user's solo-work instruction. Budget 600 seconds, no carryover. Parent sample/proof gates stay OPEN.
