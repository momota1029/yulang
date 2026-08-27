# Bracket-row grammar

## 1. Status, authority, and last verification

The Authoritative bracket-row grammar addendum is lines 15235–16040 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. Later shared caller-boundary work is in `ASOB-G` at 18358–19161.

Implementation slices are `92f662cc`, `e31ab517`, `327607a9`, `b6d4d91e`, `d25fa985`, `7252920f`, `a7c8fbd8`, `35cad71a`, and `5f627f1c`; the final listed implementation gate is `5f627f1c`.

## 2. Scope and non-scope

BracketRow is one source-bearing bracketed row used in two asymmetric positions: a leading row prefixes the mandatory ordinary type head (`[e] T`), while a trailing row is the optional argument effect of a mandatory arrow (`T [e] -> U`). Its items are full TypeExpressions.

This does not create an EffectfulType primary wrapper, an EffectArrow node, a separate row-list parser, row-tail semantics, effect inference, use-site wiring, HIR/lowering, resolver/inference, diagnostics wording, or formatting.

## 3. BNF-equivalent grammar

```text
TypeExpression := [ LeadingBracketRow TypeChainTrivia ] TypePrimary { TypeTightTail | TypeApplyArgument } [ TypeArrowBoundary TypeArrowTail ]
LeadingBracketRow := BracketRow
TypeArrowTail := [ BracketRow TypeChainTrivia ] Arrow TypeChainTrivia TypeExpression
BracketRow := LBracket BracketRowOpeningTrivia [ TypeExpression { BracketRowDelimitedBoundary TypeExpression } [ BracketRowDelimitedBoundary ] ] RBracket
BracketRowDelimitedBoundary := CommaBoundary | SemicolonBoundary | ImplicitNewlineBoundary(bracket_row_base)
```

The head after a leading row and the arrow after a trailing row are mandatory recoverable slots. `TypeChainTrivia` allows empty, same-line, or strictly-deeper trivia, never an equal-or-shallower newline between row and head/arrow.

## 4. Judge, priority, and owner boundary

In a fresh type slot, `[` is a leading-row candidate after active boundary checks and contextual/compound type starters, but before ordinary primary candidates. Once a leading row is accepted, a second leading row is disabled and recovered as a malformed mandatory head rather than parsed recursively.

After an operand is complete, the fixed-tail judge gives `[` bracket-arrow authority before TypeApply. Thus `T [e] -> U` is a trailing-row arrow and `F [e] T` is a malformed bracket-arrow tail, while `F ([e] T)` is an explicit apply argument. The row delimiter/list frame owns items and close recovery; caller stops and matching/outer closes remain unconsumed.

## 5. Byte-exact CST worked examples

The addendum provides complete source-order CST trees but no byte-range-annotated trees; no byte ranges are invented here.

```text
[e] T
```

Design lines 15726–15737 show a leading `BracketRow` as the first source-bearing child of `TypeExpression`, followed by the whitespace and ordinary head `T`.

```text
T [e] -> U
```

Design lines 15739–15756 show `BracketRow` as the first child of `TypeArrowTail`, before arrow and RHS. The whitespace before the tail remains under the enclosing `TypeExpression`.

```text
T [:] -> U
```

Design lines 15790–15809 show `:` as one `Error(Type::BracketRowItem, TypeExpression)` within the row, then an ordinary valid arrow/RHS.

```text
[e][f]T
```

Design lines 15908–15922 show only the first row node; the complete `[f]` is one `Error(Type::LeadingEffectTypeHead, TypeExpression)` before the retried head `T`.

## 6. Parser-side AST shape

`BracketRow` has exactly `open`, recovered ordered `items`, recovered `close`, and `range`. It is held by `TypeExpression.leading_effect_row` for the leading position and by `TypeArrowTail.argument_effect` for the trailing position.

`TypeExpression` has exactly `leading_effect_row`, recovered `primary`, `postfix`, optional `arrow`, and `range`. `TypeArrowTail` has exactly optional `argument_effect`, recovered `arrow`, recovered boxed `rhs`, and `range`. No `EffectfulType`, `EffectArrow`, synthetic list wrapper, or synthetic separator field exists.

The direct CST adds only `SyntaxKind::BracketRow`; it is a first source-bearing child in the leading form and a child before the arrow token in the trailing form.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| leading row followed by no head | `LeadingEffectTypeHead` Missing/Error shapes the existing recovered `TypeExpression.primary` slot |
| trailing row followed by no arrow but a valid RHS candidate | `BracketRowArrow` Missing, then same-position RHS retry |
| trailing row reaches EOF/outer boundary/newline | one `BracketRowArrow` Missing; no cascading RHS Missing |
| malformed bytes before real `->` or RHS | one maximal `BracketRowArrow` Error, then retry the arrow or RHS slot |
| malformed/absent row item | shared delimited-item Missing/Error/retry under `BracketRowItem` and separator roles |
| missing/mismatched `]` | typed `ClosingDelimiter(BracketRow)` recovery; actual outer closes are not consumed |
| second leading row | one delimiter-aware `LeadingEffectTypeHead` Error over the balanced second row, then retry the original head |

Row-internal recovery uses the shared type-delimited driver and the bracket-specific alignment policy; it does not duplicate separator, layout, delimiter, or TypeExpression parsing.

## 8. Boundary and state-restoration contract

Leading and trailing forms reuse the canonical TypeExpression episode, the bracket delimiter, `TypeDelimitedOwner::BracketRow`, local stops, and a layout frame. Every normal, recovery, and rollback exit restores delimiter, stop, layout, type-owner, and Type-ML state. Equal-or-shallower row-to-head/arrow newlines remain caller boundaries; no-row `T -> U` retains its existing CST/AST/recovery boundaries.

## 9. Yulang2 divergences

Yulang3 makes the trailing-row arrow mandatory with typed recovery, makes a leading row's head mandatory, restricts row-to-head/arrow trivia to bounded `TypeChainTrivia`, and replaces Yulang2's shared `TypeRow`/possible synthetic separators with source-bearing `BracketRow` plus raw trivia. It preserves the asymmetric NUD/LED positions, full type items, comma/semicolon/qualifying-newline row boundaries, and the leading-row/ordinary-head and trailing-row/arrow relationships.

## 10. Known residual / deferred surface

`ASOB-G` documents the general hidden caller-boundary residual; BracketRow has no construct-specific exemption beyond it. Empty/trailing-separator acceptance is explicitly recorded as an inference from the shared delimited source and EffectRow contract rather than a dedicated bare-bracket oracle fixture. Effect semantics, use-site integration, HIR/lowering, resolver/inference, diagnostics, and formatting remain deferred.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/type_expr.rs`: `parse_bracket_row`, `parse_leading_effect_type_head_for_ast`, `commit_direct_leading_effect_type_head`, `parse_bracket_arrow_tail`, `commit_direct_bracket_arrow_tail`, `bracket_arrow_pending`, `bracket_arrow_recovery_candidate`, `scan_bracket_arrow_invalid_run`, `drive_type_delimited`, `commit_direct_type_delimited`, and `scan_bracket_row_item_invalid_run`.

Fixtures include `leading_bracket_row_is_a_fresh_type_expression_prefix`, `trailing_bracket_row_is_an_arrow_effect_and_not_a_type_apply_argument`, `bracket_arrow_mandatory_slot_recovers_without_rhs_cascades`, `bracket_row_rp1_classifies_every_malformed_item_retry`, and `bracket_row_sequence_matrix_keeps_shared_normal_behavior`.
