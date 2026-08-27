# `if` / `elsif` / `else` expressions

## 1. Status, authority, and last verification

The Authoritative NUD-primary `if` / `elsif` / `else` addendum is lines 5469–6065 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. It reuses the generic colon addendum's low-level layout/block machinery but owns arm structure and arm-colon recovery itself.

The design and implementation commits are `3aaf5d80`, `2b910d47`, `5cafd19a`, and `876d11de`. The latter two add the ambient and companion-frame authority needed for current nested/control contexts.

## 2. Scope and non-scope

`if` is an operand-starting `PrimaryExpression`, not a generic colon tail. One `IfExpression` contains one initial `IfArm`, zero or more sibling `Elsif` arms, and an optional `ElseArm`. `if`/`elsif` bodies use arm-owned colon plus exactly one inline OperatorChain or an indented statement block; `else` additionally permits one bare OperatorChain.

Brace arm bodies, `case`/`catch`, other colon-owner families, declaration coverage inside blocks, conditional HIR lowering, branch typing/effects, operator association, diagnostics wording, and formatting are out of scope.

## 3. BNF-equivalent grammar

```text
IfExpression := IfArm { ArmContinuation ElsifArm } [ ArmContinuation ElseArm ]
IfArm := IfKw G* Condition Gcont ColonIntroducedArmBody
ElsifArm := ElsifKw G* Condition Gcont ColonIntroducedArmBody
Condition := OperatorChain under current-depth StopSet { Colon, LeftBrace, Elsif, Else }
ColonIntroducedArmBody := Colon G0 InlineArmExpression | Colon IndentedStatementBlock
InlineArmExpression := OperatorChain under IfContinuationStop
ElseArm := ElseKw Gcont ( ColonIntroducedArmBody | BareElseExpression )
BareElseExpression := OperatorChain under ordinary NUD-start layout and IfContinuationStop
ArmContinuation := HorizontalTrivia | NewlineTrivia where next_indent >= if_base_indent
IfContinuationStop := current outer StopSet plus Elsif plus Else
```

`elsif` is one exact contextual word. `else if` is instead a bare else body containing nested `IfExpression`.

## 4. Judge, priority, and owner boundary

At an operand-required NUD site, only the exact maximal word `if` is accepted and then cut; `ifx` remains an ordinary identifier. `elsif` and `else` are not generic NUD words: only the active IfExpression companion frame accepts them at a valid arm boundary.

Condition parsing adds Colon/LeftBrace/Elsif/Else stops, so arm colon cannot become `ColonApplicationTail`. The arm's colon and its single body are direct children of `IfArm` or `ElseArm`; inline arm bodies never use the generic colon inline-list loop. Continuation accepts horizontal trivia or newline with indentation at least the original if base; a shallower/non-keyword continuation is left to the outer owner.

## 5. Byte-exact CST worked examples

The addendum gives complete source-order CST shapes but no byte-range-annotated tree; no ranges are invented here.

```text
if x: 1 else: 0
```

Design line 6000 fixes one `IfExpression`, one `IfArm`, and one `ElseArm`, with no generic colon-tail node.

```text
if x: 1 elsif y: 2 elsif z: 3 else: 0
```

Design line 6001 fixes the first arm plus two sibling `ElsifKw` `IfArm` nodes and one `ElseArm`.

```text
if x:
  1
  2
else: 0
```

Design lines 6003–6004 fix an arm-owned `IndentedStatementBlock` with two Statement children; dedent `else` returns to the same IfExpression.

```text
else if ...
```

Design lines 5609–5611 fix this spelling as a bare `ElseArm` body containing nested IfExpression, not an `ElsifKw` sibling.

## 6. Parser-side AST shape

`PrimaryExpression::If` contains `IfExpression`. `IfExpression` has exactly ordered `arms`, optional `else_arm`, `base_indent`, and `range`.

Each `IfArm` has exactly `keyword`, recovered `condition`, recovered `body`, and `range`; `IfArmKeyword` is exactly `If` or `Elsif`. `ElseArm` has exactly `keyword`, recovered `body`, and `range`; `ElseArmBody` is exactly `Colon(ColonIntroducedArmBody)` or `Bare(Box<OperatorChain>)`.

`ColonIntroducedArmBody` has exactly recovered `colon`, recovered `rhs`, and `range`. `ArmBodyRhs` is exactly `Inline(Box<OperatorChain>)` or `Indented(IndentedStatementBlock)`.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| `if : 1` | one condition Missing before colon; colon/body commit normally |
| `if` at EOF | one condition Missing; do not cascade colon/body Missing at the same EOF |
| `if x` at EOF | retain condition and aggregate missing introducer/body as one arm-body absence |
| `if x:` at EOF | retain colon and emit one body Missing |
| wrong-indent post-colon newline | body Missing at colon; leave newline and following input to outer owner |
| malformed inline body before a value | one non-empty Error, then same body-slot retry |
| accepted `elsif`/`else` with absent body | retain keyword and emit one appropriate body Missing; never roll it back as an identifier |
| duplicate later `else` | finish after the first ElseArm and leave the second keyword to outer recovery |

All direct Missing/Error nodes are one-to-one with committed recovery records; shared indented-block recovery uses If roles rather than ColonApplication roles.

## 8. Boundary and state-restoration contract

The IfExpression captures `if_base_indent` once and keeps one companion frame through all `elsif` arms. It pops that frame before parsing its own else body, and all AST/direct normal, recovery, and rollback exits restore companion identity, stops, delimiters, indentation/layout state, and ambient ownership exactly. Nested if frames retain distinct identities.

## 9. Yulang2 divergences

Yulang3 preserves primary-expression placement, sibling `elsif` arms, optional else, colon/indent forms, and the base-indent continuation rule. It uses flat OperatorChains rather than Pratt expression subtrees, source-order direct CST without synthetic wrappers, and typed role-specific recovery rather than generic failure.

## 10. Known residual / deferred surface

The general `ASOB-G` caller-boundary residual remains characterized rather than hidden. Brace arm bodies, case/catch reuse, wider declaration statements in blocks, conditional HIR lowering, branch/result type and effect semantics, association, diagnostics, and formatting remain deferred.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/expression.rs`: `recognize_if_nud`, `parse_if_expression`, `parse_if_arm`, `parse_else_arm`, `recognize_if_arm_continuation`, `recognize_arm_colon`, `commit_if_expression`, `commit_if_arm`, `commit_else_arm`, `commit_colon_introduced_if_body`, `emit_if_missing`, and `if_body_error_retry`.

Fixtures include `if_expression_owns_arm_colons_without_colon_application_tails`, `if_expression_keeps_elsif_arms_as_siblings`, `if_expression_uses_one_companion_identity_across_every_elsif_arm`, `if_companion_frames_balance_across_ast_and_direct_recovery_exits`, `if_expression_is_binding_power_invariant`, and `if_recovery_preserves_committed_keywords_and_body_retry`.
