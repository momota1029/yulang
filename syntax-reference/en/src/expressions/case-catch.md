# `case` / `catch` expressions

## 1. Status, authority, and last verification

The Authoritative NUD-primary `case` / `catch` addendum is lines 7243–8017 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. Its arm-sequence policy owns the Case/Catch arm newlines repeatedly referenced by the Pattern pages: it is separate from Statement sequence ownership and has Case-inline, Catch-inline-single, indented, and Catch-braced policies.

The design and implementation commits are `51ccc640`, `0efd67e4`, `6e8ca889`, and `72c93d5a`. The two fixes retain scrutinee trivia/arrow recovery and same-position missing arm-separator retry in the current contract.

## 2. Scope and non-scope

`case` and `catch` are separate operand-starting NUD primaries. They own an optional apostrophe-sigil label, a flat OperatorChain scrutinee, a family-owned block, pattern arms, optional guards, exact arrows, one inline chain or an indented statement body, and Catch's optional second handler Pattern. Catch additionally owns a braced arm block.

They do not define `\case`/`\catch` lambdas, pattern forms beyond the shared Pattern grammar, case-only constructor application, case brace arm blocks, multi-arm Catch colon-inline blocks, exhaustiveness/guard/handler/label/exception semantics, HIR lowering, inference, diagnostics wording, or formatting.

## 3. BNF-equivalent grammar

```text
CaseExpression  := CaseKw  CaseLikeHead CaseBlock
CatchExpression := CatchKw CaseLikeHead CatchBlock
CaseLikeHead := G* [ CaseLikeLabel G* ] Scrutinee G0*
CaseLikeLabel := Apostrophe!Identifier

CaseBlock := Colon (CaseInlineArmSequence | CaseIndentedArmSequence)
CatchBlock := Colon (CatchInlineArmSequence | CatchIndentedArmSequence)
            | LBrace G* CatchBracedArmSequence G* RBrace

CaseArm  := Pattern [ CaseGuard ]  Arrow ArmBody [ Semicolon ]
CatchArm := Pattern [ Comma Pattern ] [ CatchGuard ] Arrow ArmBody [ Semicolon ]
CaseGuard := (IfKw | WhereKw) OperatorChain
CatchGuard := (IfKw | WhereKw) OperatorChain
ArmBody := OperatorChain | IndentedStatementBlock
```

Case and Catch scrutinees stop at Colon; Catch additionally stops at LBrace. Case has comma-separated inline arms; Catch colon-inline has exactly one arm, while its indented and braced forms can carry multiple arms. Case braced arm blocks are invalid by design.

## 4. Judge, priority, and owner boundary

At an operand-required NUD site, only exact maximal contextual words `case` and `catch` are accepted and cut; `casefold` and `catcher` remain identifiers. The `case` scrutinee reserves Colon only; the `catch` scrutinee reserves Colon and LBrace, so `case x { ... }` leaves the brace to the scrutinee/outer expression while Catch can own a direct `CatchBlock`.

Arrows are exact fixed `->` punctuation, not dynamically associated operators. Pattern, handler, guard, arrow, body, and arm separator each have their own stops. A Catch handler comma is a direct CatchArm child, whereas an arm-list comma is a family separator. Current-depth Catch-brace newlines and indented arm-indent newlines belong to the arm-sequence policy; body-statement newlines belong to the indented statement block instead.

## 5. Byte-exact CST worked examples

The addendum gives source-order CST outlines but no byte-range-annotated tree; no ranges are invented here.

```text
case 'go x: 1 if ok -> yes, _ -> no
```

Design lines 7657–7697 give the detailed `CaseExpression` outline: label, scrutinee, `CaseBlock`, guarded first `CaseArm`, `CaseArmSeparator`, and second arm are siblings in source order.

```text
catch action { err, handler -> recover; }
```

Design lines 7699–7702 fix braces as direct `CatchBlock` children. Its handler comma, second Pattern, arrow, body, and semicolon are direct `CatchArm` children; no `BracedStatementBlockExpression`, Statement, or colon tail is created.

```text
case x: 1 -> a, 2 -> b
```

Design line 7959 fixes multiple inline Case arms and optional trailing-comma coverage under `CaseInlineArmSequence`.

```text
catch action: err, handler -> recover
```

Design line 7964 fixes the exactly-one inline Catch arm with a full second handler Pattern.

## 6. Parser-side AST shape

`PrimaryExpression::Case` and `PrimaryExpression::Catch` contain `CaseExpression` and `CatchExpression`. Each has exactly `keyword`, optional `label`, recovered boxed `scrutinee`, recovered `block`, `base_indent`, and `range`; `CaseLikeLabel` has exactly `text` and `range`.

`CaseBlock` has exactly recovered `colon`, recovered `arms`, `layout`, and `range`. `CatchBlock::Colon` has exactly recovered `colon`, recovered `arms`, `layout`, and `range`; `CatchBlock::Braced` has exactly `open`, recovered `arms`, recovered `close`, and `range`. `ColonArmLayout` is exactly `Inline` or `Indented { base_indent, arm_indent }`; `ArmSequence` has exactly recovered ordered `arms` and optional `trailing_comma`.

`CaseArm` has exactly recovered `pattern`, optional recovered `guard`, recovered `arrow`, recovered `body`, optional `terminator`, and `range`. `CatchArm` adds optional recovered `handler`. `CaseGuard` and `CatchGuard` each have exactly `keyword`, recovered boxed `condition`, and `range`; `ArmGuardKeyword` is exactly `If` or `Where`; `ArmBody` is exactly inline boxed `OperatorChain` or `IndentedStatementBlock`.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| no scrutinee after keyword | one Scrutinee Missing; preserve `:`, Catch `{`, close, newline, or EOF |
| no block introducer | one Block Missing; return outer delimiter/newline/EOF untouched |
| same-or-shallower newline after colon | one Arm Missing; preserve trivia and next outer construct |
| no first pattern | one Pattern Missing; preserve handler comma, guard, arrow, close, and arm boundary |
| no Catch handler after its comma | one Handler Missing; preserve guard and arrow |
| no guard expression | one Guard Missing; preserve exact arrow and continue the arm |
| missing arrow with body NUD candidate | one Arrow Missing, then same-position body retry |
| arrow and body absent at one boundary | one root-cause record with required slot marker; preserve comma/dedent/right brace/EOF |
| missing arm comma before a next pattern | one Separator Missing, then retry that pattern once |
| malformed bytes after an arm comma | one non-empty Error, then mandatory-arm retry at the nearest safe point |
| missing Catch `}` | one CatchBlock close Missing; do not cross caller delimiter or lexical boundary |

Committed Missing/Error CST nodes are one-to-one with recovery records. Pattern recovery itself is not re-diagnosed by Case/Catch.

## 8. Boundary and state-restoration contract

The closed `ArmSequencePolicy` is the shared authority referenced by earlier Pattern pages: Case inline owns commas, Catch inline intentionally does not; indented sequences own only arm-indent newlines; Catch-braced sequences own current-brace-depth newlines and commas. This is separate from `StatementSequencePolicy`, so body-block separators cannot become arm separators.

All probes are sink-free. Normal, recovery, and rollback exits restore stop frames, delimiter/brace scope, indentation baselines, ambient ownership, and lexical-region boundaries. Nested delimiters and opaque lexical regions keep inner colon, comma, arrow, brace, `if`, and `where` spelling from becoming arm safe points.

## 9. Yulang2 divergences

Yulang3 retains contextual primary placement, labels, guards, Catch handlers, exact arrows, colon/indented forms, and direct Catch braces. It stores flat OperatorChains instead of Pratt subtrees, distinguishes family-specific source-order CST nodes rather than one generic case-like wrapper, and has typed Missing/Error recovery. Case braces are deliberately not accepted as a Case block in Yulang3.

## 10. Known residual / deferred surface

The documented `ASOB-G` residual includes representative Case/Catch arm-sequence boundary situations and remains characterized rather than hidden. Lambda forms, future Pattern forms, semantic exhaustiveness/guard/handler/label/exception behavior, other colon-owner unification, HIR lowering, inference, diagnostics, and formatting remain deferred.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/expression.rs`: `recognize_case_like_nud`, `parse_case_like_label`, `parse_catch_braced_block_ast`, `parse_case_arm_sequence_ast`, `parse_catch_arm_sequence_ast`, `arm_sequence_boundary`, `parse_case_arm_ast`, `parse_catch_arm_ast`, `parse_case_guard_ast`, `parse_catch_guard_ast`, `commit_case_like_expression`, `commit_arm_sequence`, `commit_one_arm`, `commit_arm_guard`, `commit_arm_body`, `emit_case_like_missing`, and `commit_case_like_invalid_arrow`.

Fixtures include `case_and_catch_are_primary_expressions_with_family_owned_arm_shapes`, `case_like_guards_and_indented_arms_keep_their_boundaries`, `case_like_arrow_is_exact_and_never_splits_a_longer_operator`, `case_like_ast_and_direct_paths_agree_on_arm_count_and_layout`, `case_like_missing_arrow_retries_the_body_from_the_same_position`, `case_like_recovery_marks_missing_mandatory_slots_once`, `case_like_invalid_arrow_run_recovers_to_the_next_comma_arm`, `case_like_same_indent_boundaries_stay_with_the_outer_owner`, and `case_like_missing_arm_comma_retries_the_next_pattern`.
