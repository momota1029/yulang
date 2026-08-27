# Parenthesized expression lists

## 1. Status, authority, and last verification

The historical single-expression grouped addendum is lines 3656–4098 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`; it is explicitly superseded. The authoritative uniform parenthesized-list surface is lines 4099–4351, reconciled to flat `OperatorChain` elements by the dynamic-chain addendum at 4371–5012 and given its current comma-or-newline separator rule at 9314–9693.

The implementation progression is `8551f356`, `0e3459e9`, `13564977`, `652740a6`, `00d41e51`, and `81ef211d`. `652740a6` introduced parenthesized expression lists, `00d41e51` made their elements flat chains, and `81ef211d` installed layout-aware separators.

## 2. Scope and non-scope

This page covers one uniform surface form for unit, grouping, and tuples: `()`, `(a)`, `(a,)`, and multi-element lists. The parser preserves element chains, literal trailing comma, delimiters, trivia, and recovery; inference/lowering later decides unit, grouping/identity, or tuple meaning.

It does not decide tuple runtime representation, expression semantics, type inference, HIR/lowering, formatter policy, call-argument lists, pattern/type parentheses, or a separate grouped/tuple CST kind.

## 3. BNF-equivalent grammar

```text
ParenthesizedExpression :=
    LParen OpeningTrivia
    [
        OperatorChain
        { ParenthesizedExpressionSeparator OperatorChain }
        [ ParenthesizedExpressionSeparator ]
    ]
    RParen

ParenthesizedExpressionSeparator :=
    ExplicitCommaBoundary
  | ImplicitNewlineBoundary(parenthesized_expression_base)
```

Opening trivia captures the base indentation before the first item. A newline whose following indent is equal to or shallower than that base is an implicit separator; a deeper newline remains in the current OperatorChain. Semicolon is not a valid separator.

## 4. Judge, priority, and owner boundary

The shared NUD recognizer accepts `(` sink-free and cuts only after acceptance. The parenthesized owner then pushes its delimiter, `Comma | RightParenthesis` stops, and a layout frame. Each element is an `OperatorChain` bounded at the current delimiter depth; after a completed parenthesized primary, the outer chain may continue with ordinary suffix or infix uses.

Literal comma has priority in its boundary cluster. A same-line next expression candidate without comma/newline is a missing-separator retry; a qualifying newline is already a valid separator and creates no synthetic comma or separator node. Caller-owned boundaries and nested delimiter scopes remain outside this owner.

## 5. Byte-exact CST worked examples

The relevant addenda give source forms and source-order grammar/CST ownership, but no byte-range-annotated tree; no ranges are invented here.

```text
()
```

Design line 9522 fixes this as a valid zero-element `ParenthesizedExpression`: `LParen` and `RParen`, with no element Missing.

```text
(a,)
```

Design line 9524 fixes one OperatorChain element plus a literal terminal comma. The comma is the source-bearing `trailing_comma` marker for later one-tuple interpretation.

```text
(
  a
  b
)
```

Design line 9525 fixes base indent 2, two elements, and a valid trailing implicit newline. The newlines are raw trivia, not synthetic separator nodes.

```text
(a
b)
```

Design line 9526 fixes an equal-indent newline as a valid two-element boundary.

## 6. Parser-side AST shape

The current `PrimaryExpression::Parenthesized` variant has exactly `elements: Vec<OperatorChain<'source>>`, `trailing_comma: Option<Range<usize>>`, and `range: Range<usize>`. It has no `open`, `close`, unit/group/tuple discriminator, or separator collection field.

`OperatorChain` itself has exactly `items: Vec<OperatorChainItem<'source>>` and `range: Range<usize>`. Delimiters, commas, trivia, and any recovery nodes are retained by the direct CST's single `SyntaxKind::ParenthesizedExpression` node in source order.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| immediate real `)` | valid empty list; no element Missing |
| qualifying newline between/after complete elements | valid implicit boundary; raw trivia only, no Missing comma |
| same-line next item candidate without a separator | one typed delimited-separator Missing, then same-position element retry |
| repeated comma or comma with no next item | one mandatory element Missing for the unfilled slot |
| malformed element prefix followed by a valid chain | one non-empty Error, then same-slot chain retry |
| missing/mismatched `)` | one typed parenthesized closing Missing/Error; outer boundary is not consumed |

When an initial malformed element and the close are absent at the same boundary, the direct path uses the documented non-cascading combined recovery rather than fabricating duplicate absences.

## 8. Boundary and state-restoration contract

Every normal, recovery, and rollback exit pops the parenthesis delimiter, local stop set, and `LayoutDelimitedFrame` exactly once. The base indentation is captured after opening trivia and is not recomputed from item content. AST/direct paths use the same delimiter and layout ownership; nested scopes restore the outer frame before the outer continuation resumes.

## 9. Yulang2 divergences

Yulang3 preserves one outer parenthesis/list shape and source-bearing terminal comma, but corrects Yulang2 infer-side loss of `(a,)`: one element plus a literal trailing comma is a future one-tuple rather than identity. It does not emit Yulang2's empty implicit `Separator` node, and its shared policy excludes semicolon from this list.

## 10. Known residual / deferred surface

The general missing-delimiter/caller-boundary residual is characterized by `ASOB-G`; this construct has no additional exemption. Unit/grouping/tuple classification, associated-expression lowering, type inference, runtime tuple representation, formatter policy, and other parenthesized grammars remain deferred outside this parser-surface page.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/expression.rs`: `parse_operator_chain`, `parse_direct_operator_chain`, `commit_parenthesized_nud`, `commit_parenthesized_element`, `commit_parenthesized_close`, `parenthesized_expression_stop_set`, `push_parenthesized_expression_scope`, and `pop_parenthesized_expression_scope`.

Fixtures include `operator_chain_ast_preserves_parenthesized_element_counts_and_trailing_commas`, `parenthesized_layout_boundaries_preserve_ast_direct_shape_and_trivia`, `parenthesized_layout_keeps_deeper_newlines_and_same_line_recovery_local`, `direct_chain_uses_one_parenthesized_node_for_every_valid_list_shape`, `parenthesized_primary_continues_to_outer_infix_and_suffix_uses`, and `parenthesized_elements_are_operator_chains_and_outer_continues_flatly`.
