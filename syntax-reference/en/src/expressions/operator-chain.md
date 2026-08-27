# Dynamic operator chains

## 1. Status, authority, and last verification

The Authoritative precedence-neutral dynamic-operator-chain and association-boundary addendum is lines 4371–5012 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. It also reconciles parenthesized elements to flat chains at lines 4841–4887.

The design and implementation commits are `fed0ac39` and `00d41e51`; `00d41e51` is the parser migration to precedence-neutral chains.

## 2. Scope and non-scope

The parser records source-order operator spelling and selected Prefix/Infix/Suffix/Nullfix roles in one flat `OperatorChain`, regardless of numeric binding power. Fixed structural continuations remain source-order chain items rather than target-owned application subtrees.

Numeric binding-power association, precedence-shaped application trees, HIR construction, type inference, and operator semantics belong to a later dedicated associator/lowering phase. This page does not define call, index, field, path, ML, annotation, colon, assignment, or `with:` recovery details beyond their chain-boundary role.

## 3. BNF-equivalent grammar

```text
DirectExpression := OperatorChain
OperatorChain := OperandSlot { FixedPostfixContinuation | G* SuffixUse | G* InfixUse G* OperandSlot | MlApplicationContinuation | G* TypeAnnotationContinuation } [ G* TerminalOuterContinuation ]
OperandSlot := { PrefixUse G* } Value
Value := PrimaryHead | NullfixUse
FixedPostfixContinuation := CallTail | IndexTail | FieldTail | ProjectionTail | PathTail
MlApplicationContinuation := MlArgumentSeparator MlArgument
MlArgument := OperatorChain under the ml_arg stop scope
PrefixUse := accepted operator spelling with selected role Prefix
InfixUse := accepted operator spelling with selected role Infix
SuffixUse := accepted operator spelling with selected role Suffix
NullfixUse := accepted operator spelling with selected role Nullfix
```

`OperandSlot` is parser control, not an application node. A terminal outer continuation ends the current chain; numeric binding power never chooses parser-side parent/child ownership.

## 4. Judge, priority, and owner boundary

The NUD judge selects Prefix, Nullfix, or Primary from current position, available operator capability, spelling, whitespace/layout, and value-start facts. The LED judge selects suffix/infix roles without numeric binding-power filtering. Fixed punctuation tails and ML boundaries use their own structural recognition before being represented as flat chain items.

The strong invariant is that changing only numeric binding power leaves the `OperatorChain` CST, parser AST, trivia ownership, recovery shape, and syntax diagnostics unchanged. It may change only the later associator's tree. Active stops, delimiters, structural terminators, and ambient owners are returned unconsumed.

## 5. Byte-exact CST worked examples

The addendum gives source-order CST examples but no byte-range-annotated trees; no ranges are invented here.

```text
a
```

Design lines 4545–4550 give one `OperatorChain` containing `IdentifierExpression "a"`.

```text
-a * b!
```

Design lines 4552–4564 give the fixed flat child order: Prefix use `-`, primary `a`, Infix use `*`, primary `b`, Suffix use `!`.

```text
a + b * c
```

Design lines 4566–4567 fix the same source-order CST for either relative `+`/`*` binding power; only later association differs.

```text
a!()
```

Design lines 4593–4596 fix the flat item sequence PrimaryHead `a`, SuffixUse `!`, CallTail `()` rather than a left-nested application CST.

## 6. Parser-side AST shape

`OperatorChain` has exactly `items` and `range`. Its current `OperatorChainItem` enum has exactly `PrefixUse`, `Primary`, `NullfixUse`, `InfixUse`, `SuffixUse`, `FixedPostfix`, `MlArgument { argument, range }`, `TerminalOuter`, `MissingOperand { range }`, and `Error { range }`.

`OperatorUse` has exactly `text`, `range`, and `role`; `OperatorRole` is exactly `Prefix`, `Infix`, `Suffix`, or `Nullfix`. No item records numeric binding power, a table index, a left/right operand edge, or an application subtree.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| unique dangling infix at EOF/owner boundary | retain the typed infix-use node and emit one zero-width operand Missing |
| unique dangling prefix at EOF/owner boundary | retain the typed prefix-use node and emit one zero-width operand Missing |
| invalid run before a valid operand candidate | one non-empty Error, then retry the same operand slot |
| invalid run reaches a safe boundary | one Error supplies the recovered error operand; no same-cause Missing cascade |
| valid second prefix after an infix | accept it as PrefixUse, not Error |
| unresolvable operator-shaped spelling | no invented role; existing generic recovery owns it |

Each Missing/Error node has one committed recovery record. A chain always closes after an accepted/recovered operator episode, preventing duplicate outer expression/binding absences.

## 8. Boundary and state-restoration contract

Candidate probes are sink-free; accepted roles and structural continuations cut before direct emission. Every normal, recovery, and rollback path preserves/returns the incoming stop set, delimiter and lexical-region state, ambient owner boundary, ML scope, and operator table. The parser never mutates or rebuilds the immutable `OperatorTable` per expression.

## 9. Yulang2 divergences

Yulang2 used parser-time Pratt binding-power comparisons and precedence-shaped expression CST. Yulang3 intentionally uses a BP-neutral flat surface chain and defers association. It preserves syntax-side role recognition, longest spelling, fixed structural boundaries, lossless source order, and typed mandatory-slot recovery.

## 10. Known residual / deferred surface

The documented `ASOB-G` caller-boundary residual remains characterized rather than normalized here. A dedicated HIR-side associator, association-key invalidation split, ML application's exact acceptance table, and construct-specific tail recovery details remain deferred; no second Pratt parser is retained as a competing surface authority.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/expression.rs`: `parse_operator_chain`, `parse_direct_operator_chain`, `recognize_nud`, `recognize_led`, `probe_nud`, `probe_led`, `commit_direct_operand_slot_from`, and `operator_chain_item_end`.

Fixtures include `operator_chain_ast_preserves_source_order_without_application_edges`, `direct_chain_emits_role_nodes_and_keeps_operator_trivia_outside_them`, `direct_chain_assigns_accepted_led_trivia_once`, `direct_chain_emits_suffix_and_nullfix_use_nodes`, and `operator_chain_returns_an_ambient_if_companion_gap_without_continuing`.
