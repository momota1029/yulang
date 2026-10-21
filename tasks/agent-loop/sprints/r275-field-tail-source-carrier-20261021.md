# R275 — preserve field-tail receiver and member source in ordinary HIR

Status: ACTIVE; solo primary implementation, no delegated workers.
Parent: unchanged Yulang2 Types/Console and broader playground sample goal, under Authoritative `notes/design/2026-10-20-r149-types-console.md`.
Baseline: `264fd5c38` on `research/simple-sub-intrusion`.
Authority: R149 authentic `pair.say` Display role resolution; existing Y3 `PendingFieldTailSource` and association bridge in `crates/yu-hir/src/shadow.rs`; existing ordinary local-source carrier conventions.

## Observed failure

The exact Types sample's four binding roots infer in the experimental candidate graph when used as input. Adding the unchanged final expression `pair.say` makes ordinary `yu-playground` inference return `unsupported source`. Wrapping the same expression in an admitted binding returns `candidate lowering unavailable: StructuralProjection`. `local_source::Builder::expression` accepts application tails but has no `FieldTail` case; the older ShadowArtifact retains FieldTail syntax/receiver associations, but that constructor is absent from the ordinary source carrier. This is the first evidenced implementation seam; it does not establish method resolution, typing, or sample success.

## Outcome and success evidence

Extend the ordinary local-source carrier with an explicit FieldTail form that retains the receiver child, member spelling, member source range, and FieldTail SourceNodeKey. Preserve chained-tail nesting and source order. Focused HIR tests must show `x.first.second` as two distinct source-owned tails with the original receiver chain and member identities. Lowering the exact R149 `pair.say` expression must produce the retained carrier rather than `StructuralProjection`.

Falsifiers: receiver order/identity is lost; a field-tail member is reconstructed from rendered text rather than its parse-owned token; malformed/recovered tails are admitted; any existing non-field source-carrier behavior changes.

## Exact write paths

- `crates/yu-hir/src/module/local_source.rs`
- this contract
- `notes/theory/2026-10-21-r275-field-tail-source-carrier.md`
- `tasks/agent-loop/inbox/20261021-r275-field-tail-source-carrier.md`
- primary-owned `tasks/agent-loop/current.json`
- `tasks/current.md`

No method-role selection, imported module linking, type inference result, standard-library special casing, runtime behavior, sample output, theorem closure or production promotion. Keep the exact R149 source unchanged. Continue the same broader goal after this carrier step; it is not a reduced completion target.

## Method, verification and limit

Use the retained `FieldTail` node and source token structure; preserve a distinct node per tail. Continue iteratively through the existing builder worklist. The later solver consumer remains OPEN and must consume this carrier by identity. Focused `yu-hir` source-carrier tests, `python3 tools/agent_sprint.py check`, and `git diff --check`; one heavy Cargo process. No independent review under the user's solo-work instruction.

Budget: 600 seconds, no carryover. Stop only at budget or a concrete contradiction in the R149 source constructor; record the next exact owner and keep the parent sample/proof gates OPEN.
