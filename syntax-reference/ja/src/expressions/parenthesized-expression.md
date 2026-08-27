# Parenthesized expression list

## 1. 状態・正本・最終確認

historical な single-expression grouped 追補は `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の 3656–4098 行にあり、明示的に superseded されている。Authoritative な uniform parenthesized-list surface は 4099–4351 行、flat `OperatorChain` element への reconciliation は dynamic-chain 追補 4371–5012 行、current comma-or-newline separator rule は 9314–9693 行にある。

実装 progression は `8551f356`、`0e3459e9`、`13564977`、`652740a6`、`00d41e51`、`81ef211d`。`652740a6` が parenthesized expression list、`00d41e51` が flat chain element、`81ef211d` が layout-aware separator を導入した。

## 2. 対象範囲と非対象

このページは unit/grouping/tuple を一つの uniform surface form として扱う。対象は `()`、`(a)`、`(a,)`、multi-element list である。parser は element chain、literal trailing comma、delimiter、trivia、recovery を保持し、unit/grouping/identity/tuple の意味は後段の inference/lowering が決める。

tuple runtime representation、expression semantics、type inference、HIR/lowering、formatter policy、call argument list、pattern/type parenthesis、別の grouped/tuple CST kind は対象外である。

## 3. BNF 相当の grammar

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

Opening trivia は first item 前に base indentation を capture する。following indent が base 以下の newline は implicit separator、deeper newline は current OperatorChain に残る。semicolon は valid separator ではない。

## 4. Judge・priority・owner boundary

shared NUD recognizer は `(` を sink-free で accept し、accept 後だけ cut する。parenthesized owner は delimiter、`Comma | RightParenthesis` stop、layout frame を push する。各 element は current delimiter depth で止まる `OperatorChain` であり、completed parenthesized primary 後は outer chain が ordinary suffix/infix use を続けられる。

literal comma は boundary cluster 内で priority を持つ。same-line next expression candidate が comma/newline なしで来た場合は missing-separator retry、qualifying newline は既に valid separator なので synthetic comma/separator node を作らない。caller-owned boundary と nested delimiter scope はこの owner の外に残る。

## 5. Byte-exact CST の worked examples

対応する追補は source form と source-order grammar/CST ownership を与えるが、byte-range 付き tree はない。ここでは range を作らない。

```text
()
```

設計文書 9522 行は valid zero-element `ParenthesizedExpression` を固定する。`LParen` と `RParen` だけで、element Missing はない。

```text
(a,)
```

設計文書 9524 行は OperatorChain element 一つと literal terminal comma を固定する。comma は後段の one-tuple interpretation 用の source-bearing `trailing_comma` marker になる。

```text
(
  a
  b
)
```

設計文書 9525 行は base indent 2、element 二つ、valid trailing implicit newline を固定する。newline は raw trivia であり synthetic separator node ではない。

```text
(a
b)
```

設計文書 9526 行は equal-indent newline を valid two-element boundary として固定する。

## 6. Parser 側 AST shape

current `PrimaryExpression::Parenthesized` variant は正確に `elements: Vec<OperatorChain<'source>>`、`trailing_comma: Option<Range<usize>>`、`range: Range<usize>` を持つ。`open`、`close`、unit/group/tuple discriminator、separator collection field はない。

`OperatorChain` 自身は正確に `items: Vec<OperatorChainItem<'source>>` と `range: Range<usize>` を持つ。delimiter/comma/trivia/recovery node は direct CST の単一 `SyntaxKind::ParenthesizedExpression` node が source order で保持する。

## 7. Typed recovery table

| condition | recovery と continuation |
| --- | --- |
| immediate real `)` | valid empty list。element Missing なし |
| complete element 間/後の qualifying newline | valid implicit boundary。raw trivia のみで Missing comma なし |
| separator なしの same-line next item candidate | typed delimited-separator Missing 一件後 same-position element retry |
| repeated comma または comma 後に next item がない | unfilled slot への mandatory element Missing 一件 |
| valid chain 前の malformed element prefix | non-empty Error 一件後 same-slot chain retry |
| missing/mismatched `)` | typed parenthesized closing Missing/Error 一件。outer boundary は consume しない |

initial malformed element と close が同じ boundary で欠ける場合、direct path は duplicate absence を作らない documented combined recovery を使う。

## 8. Boundary と state-restoration contract

normal/recovery/rollback の全 exit は parenthesis delimiter、local stop set、`LayoutDelimitedFrame` を exactly once pop する。base indentation は opening trivia 後に capture し、item content から再計算しない。AST/direct path は同じ delimiter/layout ownership を使い、nested scope は outer continuation 再開前に outer frame を restore する。

## 9. Yulang2 divergences

Yulang3 は one outer parenthesis/list shape と source-bearing terminal comma を保つが、Yulang2 infer-side が失った `(a,)` を修正する。one element + literal trailing comma は future one-tuple であり identity ではない。Yulang2 の empty implicit `Separator` node を出さず、shared policy はこの list から semicolon を除く。

## 10. Known residual / deferred surface

general missing-delimiter/caller-boundary residual は `ASOB-G` が characterization し、この construct は追加 exemption を持たない。unit/grouping/tuple classification、associated-expression lowering、type inference、runtime tuple representation、formatter policy、他の parenthesized grammar はこの parser-surface page の外で deferred である。

## 11. 実装と regression fixture の cross-reference

`crates/yu-syntax/src/grammar/expression.rs` では `parse_operator_chain`、`parse_direct_operator_chain`、`commit_parenthesized_nud`、`commit_parenthesized_element`、`commit_parenthesized_close`、`parenthesized_expression_stop_set`、`push_parenthesized_expression_scope`、`pop_parenthesized_expression_scope` を参照する。

fixture は `operator_chain_ast_preserves_parenthesized_element_counts_and_trailing_commas`、`parenthesized_layout_boundaries_preserve_ast_direct_shape_and_trivia`、`parenthesized_layout_keeps_deeper_newlines_and_same_line_recovery_local`、`direct_chain_uses_one_parenthesized_node_for_every_valid_list_shape`、`parenthesized_primary_continues_to_outer_infix_and_suffix_uses`、`parenthesized_elements_are_operator_chains_and_outer_continues_flatly`。
