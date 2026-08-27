# Effect-row types

## 1. Status, authority, and last verification

The Authoritative EffectRowType addendum is lines 13982–14525 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. Current shared delimited recovery is refined by `ASOB-G` at 18358–19161 and `TMN`/positional-fence authority at 16557–17289.

Implementation commits are `b0989159`, `608396fc`, `29c6a630`, `52e1853b`, and `f8b95909`. This page was checked against `063da888`.

## 2. Scope and non-scope

EffectRowType adds adjacent apostrophe-bracket forms such as `'[]`, `'[e]`, `'['e]`, `'[a, b]`, and `'[tick; 'effect]` as parser syntax. It is a nonterminal TypePrimary whose items are full TypeExpressions, separated by comma, semicolon, or qualifying newline.

Open/closed/tail classification, effect inference, annotation lowering, polymorphic variants, bracket rows, use-site wiring, HIR/lowering, diagnostics text, and formatting are out of scope.

## 3. BNF-equivalent grammar

```text
EffectRowType := Apostrophe AdjacentLBracket EffectRowOpeningTrivia [ TypeExpression { EffectRowDelimitedBoundary TypeExpression } [ EffectRowDelimitedBoundary ] ] RBracket
AdjacentLBracket := LBracket whose first byte is exactly Apostrophe.end
EffectRowDelimitedBoundary := CommaBoundary | SemicolonBoundary | ImplicitNewlineBoundary(effect_row_base)
```

The apostrophe and `[` must be adjacent. Opening trivia captures `effect_row_base` once; equal-or-shallower newline separates items, while deeper newline continues the current type item.

## 4. Judge, priority, and owner boundary

After active stops/closes and canonical NUD `for`, the primary judge probes the complete adjacent compound `"'["` before normal type-name scanning. Thus `'[` is an EffectRow candidate, while `'e` remains a sigil identifier; `' [` and `'/*c*/[e]` never cut to EffectRow.

After acceptance, the row pushes bracket delimiter, EffectRow owner, local stops, and layout frame together. It is not terminal: `'[e]::Result`, `Foo '[e]`, and `'[e] -> Out` return to the ordinary tail judge as path, apply, and arrow respectively.

## 5. Byte-exact CST worked examples

The addendum provides complete CST trees but no byte-range-annotated trees; no ranges are invented here.

```text
'[]
```

Design lines 14176–14184 show `TypeExpression > EffectRowType` with only apostrophe and bracket tokens.

```text
'[e]
```

Design lines 14186 onward show the same row node containing one full TypeExpression item; the `'[e]` spelling differs from `'['e]` only in its item token category.

```text
'[tick; 'effect]
```

The surface list is explicitly recorded at design lines 13991–13997. Semicolon is an ordinary parser separator, not a row-tail interpretation.

## 6. Parser-side AST shape

`TypePrimary::EffectRow(EffectRowType)` stores `apostrophe`, `open`, recovered ordered `items`, recovered `close`, and `range`. It records source syntax only: no parser AST field marks an open row, closed row, or tail variable.

The direct CST adds only `SyntaxKind::EffectRowType`; apostrophe, brackets, separators, trivia, and nested TypeExpression nodes remain source-order children without a synthetic item/list/tail wrapper.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| missing compound introducer | no EffectRow authority; ordinary primary recovery owns it |
| empty / valid delimited row | valid items and close; no recovery |
| leading/repeated separator | one typed EffectRow item Missing per absent item |
| same-line next item not a valid apply continuation | one typed separator Missing, then same-position item retry |
| malformed item then valid primary | one item Error, then same-slot retry |
| trailing separator before real `]` | valid trailing boundary; no empty item |
| separator before EOF/outer boundary | distinct missing item and close slots |
| missing/mismatched `]` | one EffectRow closing Missing/Error; outer close stays unconsumed |

The row reuses the shared type-delimited driver with EffectRow roles. Scanner safe points include caller boundaries, local separators, matching close, and valid retry candidates; no-cascade recovery remains typed.

## 8. Boundary and state-restoration contract

Acceptance pushes and all exits pop `Delimiter::Bracket`, `TypeDelimitedOwner::EffectRow`, row-local stops, and the layout frame exactly once. AST/direct share candidate, boundary, close, and recovery decisions. `ASOB-G`, `TMN`, and positional-fence machinery preserve ambient/If, indentation, type-owner, episode, and caller-boundary state.

## 9. Yulang2 divergences

Yulang3 preserves apostrophe-bracket rows, full type items, and comma/semicolon/layout boundaries, but requires apostrophe-bracket adjacency and does not emit Yulang2's `TypeEffectRow > TypeRow` wrappers or empty `Separator` nodes. It keeps semicolon syntactic rather than assigning row-tail meaning, and replaces generic `InvalidToken` recovery with typed slots.

## 10. Known residual / deferred surface

The general hidden-boundary residual is characterized by `ASOB-G`; no EffectRow-specific exemption broadens it. Row-tail semantics, open/closed classification, effect inference, lowering/HIR, resolver integration, diagnostics, formatting, and use-site wiring remain deferred.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/type_expr.rs`: `parse_effect_row_type`, `scan_effect_row_open`, `commit_direct_type_primary_head`, `drive_type_delimited`, `commit_direct_type_delimited`, `classify_type_delimited_recovery`, `scan_type_delimited_item_invalid_run`, and `drive_type_close_slot`.

Fixtures include `effect_row_primary_is_adjacent_semantically_blind_and_composes_normally`, `effect_row_reuses_type_call_delimited_recovery_slots`, `type_delimited_close_recovery_keeps_a_mismatched_closer_local`, and `type_close_slot_leaves_caller_owned_newlines_unconsumed`.
