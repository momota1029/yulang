# Layout-aware comma-or-newline-delimited sequence authority

## 1. Status, authority, and revision ledger

The authoritative layout-aware separator addendum is [the parser architecture design](../../../notes/design/2026-08-20-yu-syntax-chasa-architecture.md), lines 9314–9693. Its opening status predates final sign-off; the closing signature at 9692–9693 records author review and user approval. It revises the separator portions of ParenthesizedExpression (4099–4351), ColonApplication (5014–5467), Pattern core / ParenthesizedPattern (6629–7242), ListPattern (8019–8612), and RecordPattern (8613–9312). Implementation authority: `8ffd405f` and `81ef211d`.

## 2. Problem statement, scope, and non-scope

This mechanism decides whether maximal trivia between complete items is a delimiter-local comma-or-newline boundary or continuation trivia for the current item. It serves parenthesized expression lists, parenthesized/list/record patterns, call/index/projection items, delimited type items, polymorphic-variant rows, and struct field sequences. It does not make semicolon a shared separator, add a generic `Separator` node, alter an item's grammar, or decide statement/arm ownership.

## 3. Canonical rule and decision procedure

```text
DelimitedSeparator := ExplicitCommaBoundary | ImplicitNewlineBoundary(base_indent)
ImplicitNewlineBoundary(base_indent) :=
    maximal trivia run containing a physical newline
    whose following-line indentation <= base_indent
```

Capture `base_indent` once after opener trivia: use the following indent only when that trivia has a physical newline and is deeper than the incoming baseline; otherwise retain the incoming baseline. After an item: current-depth comma wins; otherwise qualifying newline is a boundary; deeper newline stays in the item; a same-line next candidate without comma gets a zero-width missing separator and same-position retry. Comma-plus-newline and newline-plus-comma each form one boundary cluster.

## 4. Authority, precedence, and ownership transfer

A local owner accepts a comma or qualifying newline only after a complete local item and only if no active outer owner reserves it. A literal comma is consumed; an implicit newline has no synthetic CST token and its raw trivia remains in the direct-CST container. Deeper newline stays with the item. Caller-owned punctuation and close return untouched; local missing separator retries at the same byte.

## 5. Worked traces and byte ownership

The revision supplies source classifications rather than byte-range CST trees, so no ranges are invented here.

| source and design-doc line | decision and ownership |
| --- | --- |
| `()` (9522) | valid empty parenthesized list |
| `(a,)` (9524) | literal trailing comma; one-tuple semantics remain literal-comma semantics |
| `(\n  a\n  b\n)` (9525) | base 2; two items; final implicit boundary is valid and creates no empty item |
| `(a\nb)` at base 0 (9526) | qualifying newline; two items and no `Missing(Comma)` |
| `(a\n  b)` at base 0 (9527) | deeper trivia remains in the first `OperatorChain`; `b` is not a second item |

The same revision covers `[]`, `[a,]`, and `[a\nb]` (9573–9578); its in-place RecordPattern revision restores `{a\nb}` at 9630.

## 6. Participating parser state and adoption matrix

| state/type | producer | query / consumer | observable effect |
| --- | --- | --- | --- |
| `LayoutDelimitedFrame` | `LayoutDelimitedFrame::after_opening_trivia` / `LayoutDelimitedFrame::inline` | `LayoutDelimitedFrame::boundary_after_trivia` | captured base only; no AST node |
| `LayoutDelimitedBoundary` | frame query | item/separator drivers | `ImplicitNewline`, `DeeperNewline`, or `None`; no synthetic separator |
| `IndentationBaseline` | ParseLocal indentation scope | frame construction | incoming indentation identity |
| `StopSet` and `StopKind` | caller grammar frame | local/outer boundary checks | caller stops remain visible |
| `Delimiter` | delimiter stack | close judge | separates local and outer close ownership |

Adopters use `push_layout_delimited_baseline` / `pop_layout_delimited_baseline`, `push_pattern_layout_baseline` / `pop_pattern_layout_baseline`, `push_layout` / `pop_layout`, and `push_struct_layout` / `pop_struct_layout` in their respective grammar files.

## 7. Recovery, cardinality, and no-cascade contract

Qualifying newline between items or before close is valid and emits neither Missing nor Error. Deeper newline remains with the item. Same-line next item without comma emits one zero-width missing separator and retries. Repeated comma and semicolon keep construct-specific recovery; semicolon remains invalid. Direct CST records source tokens/raw trivia only, never a source-absent separator; one cause never cascades to a second separator error.

## 8. Lifecycle, rollback, and invariants

Capture and push the frame at opener/inline entry; pop it on every normal, recovery, and rollback exit. Never recompute base from later content, error ranges, or EOF. Nested owners restore the outer frame before the caller resumes, and AST/direct paths make the same decision.

## 9. Yulang2 divergences

Equal-or-shallower physical newlines are first-class implicit separators, including a trailing implicit boundary before close. No literal comma is fabricated and existing literal trailing-comma AST semantics remain unchanged.

## 10. Known residuals, exclusions, and extension rule

The mechanism does not settle a boundary already owned by an ambient statement/arm owner or caller stop; ASOB documents that layer. A future delimited construct must declare its item grammar, frame/base capture, close/stop ownership, and trailing-separator rule, then reuse this query rather than rescan raw newlines privately.

## 11. Implementation, fixtures, and consumer-page cross-reference

Core implementation: `LayoutDelimitedFrame`, `LayoutDelimitedBoundary`, `LayoutDelimitedFrame::after_opening_trivia`, and `LayoutDelimitedFrame::boundary_after_trivia`. Fixtures: `parenthesized_layout_boundaries_preserve_ast_direct_shape_and_trivia`, `parenthesized_patterns_accept_comma_or_layout_newline_boundaries`, `list_patterns_accept_comma_or_layout_newline_and_keep_spread_items`, `type_groups_reuse_layout_boundaries_without_synthetic_separator_nodes`, `named_record_types_are_primary_fields_with_comma_or_newline_boundaries`, and `struct_named_brace_fields_keep_their_own_layout_and_type_apply_boundary`.

Consumer summaries: [parenthesized expressions](../expressions/parenthesized-expression.md), [colon application](../expressions/colon-application.md), [call/field/path tails](../expressions/call-field-path-tails.md), [index/projection tails](../expressions/index-projection-tails.md), [Pattern core](../patterns/pattern-core.md), [list patterns](../patterns/list-pattern.md), and [record patterns](../patterns/record-pattern.md).
