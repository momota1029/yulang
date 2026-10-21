# R275 rev2 — retain FieldTail across HIR, solver and runtime consumers

Revision reason: the next direct `yu-playground` check found two exhaustive runtime-program consumers of `LocalSourceForm`. Add identity-preserving traversal and explicit unsupported-runtime reporting. Initial and rev1 contracts remain immutable.

Status: ACTIVE; solo primary implementation, no delegated workers.
Parent: unchanged Yulang2 Types/Console and broader playground sample goal, under Authoritative `notes/design/2026-10-20-r149-types-console.md`.
Baseline: `264fd5c38` plus the in-progress R275 source/solver changes.
Authority: R149 authentic `pair.say` Display role resolution; existing Y3 `PendingFieldTailSource` and association bridge; existing local-source and runtime constructors.

## Outcome and evidence

The exact Types binding prefix infers, while the final unchanged `pair.say` fails `unsupported source`; the same expression in an admitted binding previously failed HIR `StructuralProjection`. Ordinary local source now retains each FieldTail's receiver, member spelling, member range and tail source identity. The solver visits the receiver and explicitly returns unavailable at FieldTail construction until authentic method-role resolution exists. The runtime-program adapter explicitly reports unsupported FieldTail if called without that solver gate, and diagnostic traversal descends through the receiver.

Focused HIR tests cover exact Types source and chained `base.first.second`, asserting member tokens, source occurrence ownership and receiver order. `cargo check -p yu-playground` must compile. Exact sample inference is still expected to fail closed at unresolved role selection; do not claim Types/Console success.

Falsifiers: receiver order/identity is lost; member identity is reconstructed from display text; malformed/recovered tails are admitted; the candidate solver fabricates a member type or accepts without role evidence; runtime treats unresolved field/method selection as a value.

## Exact write paths

- `crates/yu-hir/src/module/local_source.rs`
- `crates/yu-solver/src/candidate_source.rs`
- `tools/inference-playground/src/runtime/program.rs`
- this revision contract
- `notes/theory/2026-10-21-r275-field-tail-source-carrier.md`
- `tasks/agent-loop/inbox/20261021-r275-field-tail-source-carrier.md`
- primary-owned `tasks/agent-loop/current.json`
- `tasks/current.md`

No role selection, imported module linking, public type export, runtime execution, sample output, theorem closure or production promotion. Keep exact R149 source unchanged and continue the broader goal after this prerequisite.

## Verification and limit

Focused HIR test, `cargo check -p yu-playground`, exact unchanged Types CLI probe, sprint static check and `git diff --check`. One heavy Cargo process, no independent review under user-directed solo work. Budget 600 seconds, no carryover. All parent sample/proof gates remain OPEN.
