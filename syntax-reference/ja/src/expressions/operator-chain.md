# Dynamic operator chain

## 1. 状態・正本・最終確認

Authoritative な precedence-neutral dynamic-operator-chain / association-boundary 追補は `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の 4371–5012 行にある。parenthesized element を flat chain へ reconcile する箇所は 4841–4887 行にある。

design / implementation commit は `fed0ac39` と `00d41e51`。`00d41e51` は parser を precedence-neutral chain へ migration した。

## 2. 対象範囲と非対象

parser は numeric binding power に関係なく、source-order operator spelling と selected Prefix/Infix/Suffix/Nullfix role を一つの flat `OperatorChain` に記録する。fixed structural continuation も target-owned application subtree ではなく source-order chain item に留まる。

numeric binding-power association、precedence-shaped application tree、HIR construction、type inference、operator semantics は後段の dedicated associator/lowering phase が所有する。このページは call/index/field/path/ML/annotation/colon/assignment/`with:` の recovery detail を、chain-boundary role を超えて定義しない。

## 3. BNF 相当の grammar

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

`OperandSlot` は parser control であり application node ではない。terminal outer continuation は current chain を終え、numeric binding power は parser-side parent/child ownership を選ばない。

## 4. Judge・priority・owner boundary

NUD judge は current position、available operator capability、spelling、whitespace/layout、value-start fact から Prefix/Nullfix/Primary を選ぶ。LED judge は numeric binding-power filter なしに suffix/infix role を選ぶ。fixed punctuation tail と ML boundary は own structural recognition を使い、flat chain item として表す。

strong invariant は numeric binding power だけを変えても `OperatorChain` CST、parser AST、trivia ownership、recovery shape、syntax diagnostic が不変なことだ。変化してよいのは後段 associator の tree だけである。active stop、delimiter、structural terminator、ambient owner は consume せず返す。

## 5. Byte-exact CST の worked examples

追補は source-order CST example を持つが byte-range 付き tree はない。ここでは range を作らない。

```text
a
```

設計文書 4545–4550 行は `IdentifierExpression "a"` 一つを持つ `OperatorChain` を与える。

```text
-a * b!
```

設計文書 4552–4564 行は Prefix use `-`、primary `a`、Infix use `*`、primary `b`、Suffix use `!` の fixed flat child order を与える。

```text
a + b * c
```

設計文書 4566–4567 行は `+`/`*` の relative binding power がどちらでも同じ source-order CST とし、後段 association だけを変える。

```text
a!()
```

設計文書 4593–4596 行は left-nested application CST ではなく PrimaryHead `a`、SuffixUse `!`、CallTail `()` の flat item sequence を固定する。

## 6. Parser 側 AST shape

`OperatorChain` は正確に `items` と `range` を持つ。current `OperatorChainItem` enum は正確に `PrefixUse`、`Primary`、`NullfixUse`、`InfixUse`、`SuffixUse`、`FixedPostfix`、`MlArgument { argument, range }`、`TerminalOuter`、`MissingOperand { range }`、`Error { range }` を持つ。

`OperatorUse` は正確に `text`、`range`、`role` を持つ。`OperatorRole` は正確に `Prefix`、`Infix`、`Suffix`、`Nullfix` である。numeric binding power、table index、left/right operand edge、application subtree を記録する item はない。

## 7. Typed recovery table

| condition | recovery と continuation |
| --- | --- |
| EOF/owner boundary の unique dangling infix | typed infix-use node を保持し zero-width operand Missing 一件 |
| EOF/owner boundary の unique dangling prefix | typed prefix-use node を保持し zero-width operand Missing 一件 |
| valid operand candidate 前の invalid run | non-empty Error 一件後 same operand slot retry |
| safe boundary へ達する invalid run | Error 一件が recovered error operand となり same-cause Missing cascade なし |
| infix 後の valid second prefix | Error ではなく PrefixUse として accept |
| resolve 不能な operator-shaped spelling | role を作らず existing generic recovery が所有 |

Missing/Error node ごとに committed recovery record は一件である。accepted/recovered operator episode 後も chain は必ず close し、outer expression/binding absence の重複を防ぐ。

## 8. Boundary と state-restoration contract

candidate probe は sink-free であり、accepted role/structural continuation は direct emission 前に cut する。normal/recovery/rollback の全 path は incoming stop set、delimiter/lexical-region state、ambient owner boundary、ML scope、operator table を preserve/return する。parser は immutable `OperatorTable` を expression ごとに mutate/rebuild しない。

## 9. Yulang2 divergences

Yulang2 は parser-time Pratt binding-power comparison と precedence-shaped expression CST を使った。Yulang3 は意図的に BP-neutral flat surface chain を使い association を defer する。syntax-side role recognition、longest spelling、fixed structural boundary、lossless source order、typed mandatory-slot recovery は保つ。

## 10. Known residual / deferred surface

documented `ASOB-G` caller-boundary residual はここでも characterization のままである。dedicated HIR-side associator、association-key invalidation split、ML application の exact acceptance table、construct-specific tail recovery detail は deferred であり、競合する second Pratt parser は残さない。

## 11. 実装と regression fixture の cross-reference

`crates/yu-syntax/src/grammar/expression.rs` では `parse_operator_chain`、`parse_direct_operator_chain`、`recognize_nud`、`recognize_led`、`probe_nud`、`probe_led`、`commit_direct_operand_slot_from`、`operator_chain_item_end` を参照する。

fixture は `operator_chain_ast_preserves_source_order_without_application_edges`、`direct_chain_emits_role_nodes_and_keeps_operator_trivia_outside_them`、`direct_chain_assigns_accepted_led_trivia_once`、`direct_chain_emits_suffix_and_nullfix_use_nodes`、`operator_chain_returns_an_ambient_if_companion_gap_without_continuing`。
