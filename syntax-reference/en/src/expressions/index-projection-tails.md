# Index and projection tails

## 1. Status, authority, and last verification

The Authoritative IndexTail/ProjectionTail fixed-tail addendum is lines 10184–10660 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. It completes the body, adjacency, delimiter ownership, and recovery intentionally deferred by the Call/Field/Path/ML addendum at lines 9695–10182.

The design and implementation series is `5f5416ea`, `8d3d22e2`, `5f067e33`, `0ea6bf5e`, `a6926e9d`, `6b39d612`, `4315dd90`, and `f3c28bc5`.

## 2. Scope and non-scope

This page defines adjacent IndexTail, tuple ProjectionTail, and record ProjectionTail as target-free source-order fixed postfixes. Their bodies contain general OperatorChains, layout-aware comma/semicolon/newline item lists, and owner-safe close recovery; record projection alone accepts exact `..` spread items.

Field, Call, Path, and ML recognition remain shared adjacent-tail infrastructure. Semantic index/projection evaluation, record validation, spread position/multiplicity rules, target association, HIR lowering, inference, diagnostics wording, and formatting are out of scope.

## 3. BNF-equivalent grammar

```text
FixedPostfixTail += IndexTail | ProjectionTail

IndexTail := LBracket G* [ OperatorChain { IndexSeparator OperatorChain } [ IndexSeparator ] ] RBracket
ProjectionTail := ProjectionTupleTail | ProjectionRecordTail
ProjectionTupleTail := Dot LParen G* [ OperatorChain { ProjectionTupleSeparator OperatorChain } [ ProjectionTupleSeparator ] ] RParen
ProjectionRecordTail := Dot LBrace G* [ ProjectionRecordItem { ProjectionRecordSeparator ProjectionRecordItem } [ ProjectionRecordSeparator ] ] RBrace
ProjectionRecordItem := OperatorChain | ProjectionRecordSpreadItem
ProjectionRecordSpreadItem := DotDot G* OperatorChain

IndexSeparator := Comma | Semicolon | ImplicitNewlineBoundary(index_base)
ProjectionTupleSeparator := Comma | Semicolon | ImplicitNewlineBoundary(tuple_projection_base)
ProjectionRecordSeparator := Comma | Semicolon | ImplicitNewlineBoundary(record_projection_base)
```

Index requires no trivia before `[`. Projection requires adjacent dot/opener, while dot-leading `ChainContinuingTrivia` follows FieldTail's continuation rule. Only record-projection item position gives exact `..` fixed spread authority; index and tuple contents treat it as ordinary dynamic syntax when accepted there.

## 4. Judge, priority, and owner boundary

Active owner stops, outer matching closes, equal-or-shallower newline, and accepted dynamic spelling win before a structural tail. With no leading trivia, `[` selects IndexTail. Exact `.(` and `.{` select projection before FieldTail; `a. (x)` and `a. {x}` are not projections. A fixed tail cuts after its introducer and returns to the shared operand-complete loop only after its own close/recovery.

Index owns Bracket plus comma/semicolon/right-bracket stops; tuple projection owns Parenthesis plus comma/semicolon/right-parenthesis; record projection owns Brace plus comma/semicolon/right-brace. Each is an `ExpressionDelimitedOwner`, so inner colon application takes one RHS and returns the container boundary; qualifying ML continuation remains local to one item while equal-or-shallower newline returns to the container.

## 5. Byte-exact CST worked examples

The addendum gives source-order CST trees but no byte-range-annotated tree; no ranges are invented here.

```text
a[i; j].(x, y).{left: value, ..rest}
```

Design lines 10396–10430 give the complete tree: distinct IndexTail, ProjectionTupleTail, and ProjectionRecordTail siblings directly own their delimiters, general-expression items, punctuation, and close.

```text
a[0]
```

Design line 10216 records the historical single-index fixture preserved by the tail grammar.

```text
a.(x)
```

Design lines 10284–10285 fix adjacent dot/opener recognition as projection rather than FieldTail.

```text
a.{..left, middle, ..right}
```

Design lines 10496–10499 fix record projection's parser-valid first/middle/last multiple spread items, each with a `ProjectionRecordSpreadItem` rather than field syntax.

## 6. Parser-side AST shape

`FixedPostfixTail` adds `Index(IndexTail)` and `Projection(ProjectionTail)`. `IndexTail` has exactly `open`, ordered `items`, recovered `close`, and `range`.

`ProjectionTail` is exactly `Tuple(ProjectionTupleTail)` or `Record(ProjectionRecordTail)`. `ProjectionTupleTail` has exactly `dot`, `open`, ordered `items`, recovered `close`, and `range`. `ProjectionRecordTail` has exactly `dot`, `open`, ordered `items`, recovered `close`, and `range`.

`ProjectionRecordItem` is exactly `Expression(OperatorChain)` or `Spread(ProjectionRecordSpreadItem)`. `ProjectionRecordSpreadItem` has exactly `marker`, recovered boxed `rhs`, and `range`. No AST type duplicates separator punctuation/trivia, and no generic Projection CST wrapper exists.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| `a[]`, `a.()`, or `a.{}` | valid empty tail; no Missing |
| leading/repeated comma or semicolon | one zero-width missing item before punctuation, retain punctuation, then retry |
| same-line next NUD without a separator | one zero-width missing separator, then same-position retry; valid ML remains one item |
| malformed item before ordinary NUD/spread | one maximal non-empty item Error, then same-slot retry |
| missing matching close at EOF/caller boundary | one zero-width close Missing; leave boundary untouched |
| stray mismatched close | preserve caller-owned close; otherwise consume one closing Error and continue this close slot |
| `a.{..}` or `a.{.., next}` | retain marker and emit one spread-RHS Missing without consuming separator/close |
| `a.{..@rest}` | one non-empty spread-RHS Error, then retry `rest` in the same RHS slot |
| `a.{...rest}` / `a.{..+rest}` | do not split longer spelling into DotDot; leave it to ordinary malformed/dynamic authority |
| malformed colon tail inside item | nested ColonApplicationTail recovers once; projection emits no duplicate record |

All Missing nodes are zero-width, Errors are maximal non-empty ranges, and one committed recovery node has one diagnostic identity.

## 8. Boundary and state-restoration contract

Each accepted opener pushes its matching delimiter, item stops, indentation baseline, and typed expression-delimited owner, then pops every frame exactly on normal, recovery, and rollback exits. The owner frame distinguishes otherwise same-delimiter constructs such as ParenthesizedExpression versus tuple projection and BracedStatementBlock versus record projection. Nested punctuation, lexical regions, ambient boundaries, outer closes, and equal-or-shallower newlines are not consumed by an item recovery scanner.

## 9. Yulang2 divergences

Yulang3 removes Yulang2's `Index > Bracket`, `ProjectionTuple > Paren`, and `ProjectionRecord > BraceGroup` wrapper layers: its typed tail nodes own delimiters/items/closes directly. It uses raw separator bytes rather than separator wrappers, typed Missing/Error recovery, exact maximal DotDot rather than splitting longer spellings, and names tails by their chain role. Source acceptance for adjacency, general expression content, semicolons, and record-only spread remains aligned.

## 10. Known residual / deferred surface

The documented `ASOB-G` caller-boundary residual remains characterized rather than hidden. Semantic index/projection meaning, record shape/type validation, spread position/multiplicity validation, target association, HIR lowering, inference, diagnostics, and formatting remain deferred.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/expression.rs`: `recognize_fixed_postfix`, `parse_fixed_postfix_tail`, `parse_index_tail`, `parse_projection_tuple_tail`, `parse_projection_record_tail`, `parse_projection_items_ast`, `commit_fixed_postfix_tail`, `commit_index_tail`, `commit_projection_tuple_tail`, `commit_projection_record_tail`, `commit_projection_items`, `index_item_error_retry`, `projection_item_error_retry`, `emit_index_missing`, `emit_projection_missing`, and `emit_projection_close_missing`.

Fixtures include `index_tails_are_flat_layout_delimited_and_bp_neutral`, `index_tail_requires_adjacency_and_recovers_locally`, `index_tail_restores_owner_frames_and_precedes_terminal_colon`, `projection_tails_precede_field_dispatch_and_keep_general_expression_items`, `projection_tail_recovery_keeps_typed_slots_local`, `projection_tail_close_recovery_is_owner_safe_on_both_paths`, and `record_projection_rejects_non_exact_spread_spellings`.
