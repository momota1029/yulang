# Standalone TypeExpression core

## 1. Status, authority, and last verification

The Authoritative standalone TypeExpression core addendum is lines 12155–12866 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. Later `TMN` newline-owner policy and positional-fence implementation authority refine shared recovery at 16557–16861 and 16862–17289 without making TypeExpression depend on Pattern or `OperatorTable`.

Core implementation commits are `b24a3e90`, `3bc6e108`, `c5896444`, and `5a375dfd`; recovery follow-ups include `d99d49e7`, `72948621`, `42c1544c`, and `2c4d7540`. This page was checked against `5df7ace1`.

## 2. Scope and non-scope

The core owns identifier/sigil/number atoms, `::` paths, adjacent calls, whitespace ML-style application, fixed right-associative arrows, and parenthesized/tuple-like groups. It is a standalone fixed-precedence grammar owner, architecturally parallel to Pattern grammar rather than an expression `OperatorChain` variant.

`for`, named records, polymorphic variants, effect rows, bracket rows, declaration use-site wiring, typing, HIR/lowering, diagnostics text, and formatting are outside the original core scope. Later authoritative addenda supply the exotic primaries separately.

## 3. BNF-equivalent grammar

```text
TypeExpression := TypePrimary { TypeTightTail | TypeApplyArgument } [ TypeArrowTail ]
TypePrimary := TypeAtom | ParenthesizedTypeGroup
TypeAtom := Identifier | SigilIdentifier | Number
TypeTightTail := TypePathTail | TypeCallTail
TypePathTail := TypeChainTrivia ColonColon TypeChainTrivia TypePathSegment
TypePathSegment := Identifier | SigilIdentifier
TypeCallTail := LParen OpeningTrivia [ TypeExpression { TypeDelimitedSeparator TypeExpression } [ TypeDelimitedSeparator ] ] RParen
TypeApplyArgument := TypeApplyBoundary TypeExpressionInTypeMlScope
TypeArrowTail := TypeChainTrivia Arrow TypeChainTrivia TypeExpression
ParenthesizedTypeGroup := LParen OpeningTrivia [ TypeExpression { TypeDelimitedSeparator TypeExpression } [ TypeDelimitedSeparator ] ] RParen
TypeDelimitedSeparator := CommaBoundary | SemicolonBoundary | ImplicitNewlineBoundary(type_delimited_base)
```

`Number` is a valid primary but never a path segment. A qualifying newline separates delimited items; a deeper newline is type continuation.

## 4. Judge, priority, and owner boundary

The tail judge first yields to an active stop, close, or equal-or-shallower caller boundary. With no leading trivia it then recognizes exact `->`, adjacent `(`, and exact `::`. In `type_ml_arg`, non-empty trivia ends the nested argument before whitespace arrow/path probing. Then trivia-qualified arrow, path, and a candidate-backed `TypeApplyArgument` are considered.

Thus `List(Int)` is a call while `List (Int)` is an apply; `F A::B` keeps the path inside the applied argument, while `F A ::B` gives it to the outer type. Arrow accepts a full RHS and ends the current loop, so `A -> B -> C` is right-associative. No dynamic binding-power table participates.

## 5. Byte-exact CST worked examples

The addendum contains complete CST trees but no byte-range-annotated trees; no ranges are invented here.

```text
List(Int)::Result Arg -> Out -> Final
```

Design lines 12324–12353 show one source-order `TypeExpression`: `TypeCallTail`, `TypePathTail`, `TypeApplyArgument`, and a `TypeArrowTail` whose RHS has the second arrow tail. Whitespace belongs to the apply/arrow owners.

```text
(A)
```

Design lines 12366–12369 classify this as a one-element grouped type, unlike `(A,)` and `(A;)`, which are tuple-like because their literal trailing separator is retained.

```text
F A -> B
```

Design lines 12488–12500 fix this as `(F A) -> B`; the contrasting `F A->B` is `F (A -> B)` because the nested ML argument sees no trivia before its arrow.

## 6. Parser-side AST shape

`TypeExpression` holds `primary`, ordered `postfix`, optional `arrow`, and `range`. Core postfix variants are `TypePostfixTail::{Path, Call, Apply}`. `TypeCallTail` and `ParenthesizedTypeGroup` retain recovered elements and close slots; groups additionally retain a literal `trailing_explicit_separator` for grouping-versus-tuple classification.

The current `TypePrimary` enum has later exotic variants too, but the core forms remain `Atom` and `Parenthesized`. `TypeApplyArgument` owns its accepted trivia `boundary` and boxed argument; arrow owns recovered RHS rather than rewriting precedence into a left-nested AST.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| missing mandatory primary | one `TypeRole::Primary` Missing; caller boundary remains unconsumed |
| malformed primary then valid primary | one non-empty Primary Error, then same-slot retry |
| `::` without a segment | one `TypeRole::PathSegment` Missing; boundary remains owned |
| malformed path segment | one PathSegment Error; numeric segment is not accepted |
| missing call/group item or separator | one typed item/separator Missing, then same-position retry |
| accepted call/group with missing close | one closing-delimiter Missing; no reinterpretation as another form |
| `->` missing/malformed RHS | one `TypeRole::ArrowRhs` Missing/Error; outer boundary remains unconsumed |
| no primary after apply trivia | no apply authority and no synthetic Missing |

All scanners stop before active stops, closes, delimiters, separators, qualifying newline, and valid retry candidates. `TMN-C` and the positional fence preserve this contract for malformed newline-bearing trivia without cascade.

## 8. Boundary and state-restoration contract

Candidate probes are sink-free and state-neutral. Accepted calls/groups synchronize delimiter, stop, layout base, and `TypeDelimitedOwner`; applies push only `type_ml_arg`. Normal, recovery, and rollback exits restore those states, including TypeExpression episode and positional-fence state. AST/direct parsing shares the same candidate, layout, cut, and safe-point decisions.

## 9. Yulang2 divergences

Yulang3 preserves fixed tails, ML scope behavior, and right-associative arrows, but uses literal newline trivia instead of empty `Separator` nodes. It replaces generic `InvalidToken` recovery with typed Missing/Error and owner-safe boundaries. It deliberately excludes numeric path segments, avoids generic wrapper nodes, and provides a one-site outer missing-role override.

## 10. Known residual / deferred surface

Hidden caller-boundary cases behind missing nested delimiters are characterized by later `ASOB-G` and Cast work rather than normalized away. Core deliberately deferred exotic primaries and all declaration/pattern use-site integrations; those now have or require separate authoritative addenda.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/type_expr.rs`: `parse_type_expression`, `parse_required_type_expression_with_recovery_context`, `commit_direct_type_expression`, `commit_direct_type_expression_with_recovery_context`, `parse_type_call_tail`, `parse_parenthesized_type_group`, `parse_type_arrow_tail`, `commit_direct_type_delimited`, `classify_type_malformed_trivia`, and `scan_type_item_invalid_run_with_disposition`.

Fixtures include `type_core_forms_keep_fixed_flat_structure`, `type_arrow_is_right_associative_without_an_operator_table`, `type_call_and_group_accept_comma_and_semicolon`, `type_groups_reuse_layout_boundaries_without_synthetic_separator_nodes`, `type_apply_uses_one_argument_per_nonempty_trivia_boundary`, `path_and_arrow_missing_rhs_leave_an_outer_layout_newline_unconsumed`, and `type_call_missing_item_and_close_keep_distinct_typed_slots`.
