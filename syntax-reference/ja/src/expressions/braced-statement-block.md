# Brace-delimited statement block

## 1. 状態・正本・最終確認

Authoritative な NUD-primary brace-delimited statement-block 追補は `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の 6067–6627 行にある。末尾 signature は Claude 査読・ユーザ承認を記録している。

design / implementation commit は `04ebde8e`、`2c9a77b8`、`9f0d9d88`。implementation は brace primary と indented block が outer ownership を統合せずに共有する closed statement-sequence policy を導入した。

## 2. 対象範囲と非対象

operand-required NUD site の `{ ... }` は `BracedStatementBlockExpression`、すなわち brace で囲まれた zero-or-more canonical Statement である。surrounding flat `OperatorChain` の primary 一つであり、comma、semicolon、returned physical newline の Statement separator と三種すべての trailing form を許す。

record literal/field node、`if` や declaration の brace body、projection record、fixed brace-local spread item、rule/use/interpolation brace、`CatchBlock`、HIR の block/record interpretation、inference、diagnostics wording、formatting は対象外である。

## 3. BNF 相当の grammar

```text
BracedStatementBlockExpression :=
    LBrace OpeningTrivia
    [ Statement { BraceStatementSeparator Statement } [ BraceStatementSeparator ] ]
    ClosingTrivia RBrace

BraceStatementSeparator := G0 Comma G* | G0 Semicolon G* | Gnl
OpeningTrivia := G*
ClosingTrivia := G0
```

`Gnl` は completed current-depth Statement の後に return した trivia だけである。deeper continuation newline はその Statement 内に残る。block は empty-valid であり、optional final position の separator は empty Statement を作らない。

## 4. Judge・priority・owner boundary

sink-free NUD judge は lone fixed `{` だけを accept し、cut 後に total block continuation を所有する。`Delimiter::Brace`、local `Comma`/`Semicolon`/`RightBrace` stop、bracketed inline mode、braced ambient-owner barrier を push し、outer condition/comma/close stop は scope exit まで suspend する。

brace owner は Statement slot 前と separator 後で matching `}` を認識する。Statement separator と close recovery はこの owner だけが持つ。`{x: 1, y: 2}` では brace-owned comma が ordinary `ColonApplicationTail` を RHS 一つで止め、parser は `RecordLiteral`/`RecordField` を作らない。

## 5. Byte-exact CST の worked examples

追補は source-order CST tree を示すが byte-range 付き tree はない。ここでは range を作らない。

```text
{}
```

設計文書 6219、6495 行は valid empty block を記録する。`LBrace`、あれば opening/closing trivia、`RBrace` だけであり、synthetic Statement/separator/Missing node はない。

```text
{x,y}
```

設計文書 6220–6222、6561–6563 行は comma `BlockStatementSeparator` 一つで分かれた `Statement > OperatorChain` child 二つを記録する。

```text
{x,}
```

設計文書 6224、6499 行は Statement 一つと valid trailing comma separator、`Missing(statement)` なしを記録する。

```text
{x: 1, y: 2}
```

設計文書 6116、6259、6536 行は outer `BracedStatementBlockExpression` を固定する。comma は block separator であり、inner Statement 二つは ordinary one-argument `ColonApplicationTail` で終わる。

## 6. Parser 側 AST shape

`PrimaryExpression::BracedStatementBlock` は `BracedStatementBlockExpression` を持つ。この struct は正確に `open`、recovered ordered `statements`、recovered `close`、`range` を持つ。

comma/semicolon/newline/trailing-separator spelling を AST は duplicate しない。それらの byte は source-order CST child に残り、recovered close は matching brace range または committed missing slot を保持する。

## 7. Typed recovery table

| condition | recovery と continuation |
| --- | --- |
| EOF の `{` | empty body は valid。zero-width close Missing 一件だけ |
| EOF の `{x` | Statement を保持し close Missing 一件 |
| EOF の `{x,` | trailing comma は valid。close Missing 一件だけ |
| separate second Statement candidate を持つ `{x y}` | separator Missing 一件を zero-width で置き、`y` を next Statement として retry |
| `{x,,y}` | post-comma mandatory Statement を recover。empty Statement を accept しない |
| `{x,@ y}` | non-empty statement Error 一件後、`y` から same-slot retry |
| `{x]}` | `]` を closing-delimiter Error 一件として consume し、この block の `}` 探索を続ける |
| `}` 前の owner/root safe point | consume せず zero-width close Missing |

Missing node はすべて zero-width、Error は non-empty maximal episode、committed recovery node 一つは diagnostic identity 一つである。

## 8. Boundary と state-restoration contract

全 AST/direct exit は incoming delimiter stack、stop set、`ml_arg`、inline mode、ambient-owner/If-companion visibility state を restore する。braced barrier は current-depth newline sequence authority を所有し、nested lexical region/delimiter は outer block に separator/close を渡せない。これは後の ASOB barrier が reuse する brace-owned sequence authority であり、outer node authority はこの construct に残る。

## 9. Yulang2 divergences

Yulang3 は ordinary brace-primary statement block、empty validity、comma/semicolon/newline separator、trailing separator を保つ。overloaded Yulang2 `BraceGroup` を primary-only `BracedStatementBlockExpression` へ置き換え、Pratt subtree ではなく flat `OperatorChain` Statement を保持し、synthetic newline separator token と historical fixed `ExprSpread` を追加しない。

## 10. Known residual / deferred surface

documented `ASOB-G` caller-boundary residual は hidden にせず characterize する。brace-specific spread、record/block/argument interpretation、declaration/control-flow brace body、projection/rule/use/interpolation form、HIR lowering、inference、diagnostics、formatting は deferred または固有 owner grammar の責務である。

## 11. 実装と regression fixture の cross-reference

`crates/yu-syntax/src/grammar/expression.rs` では `recognize_braced_statement_block_open`、`recognize_braced_statement_block_close`、`parse_braced_statement_block_expression`、`braced_statement_block_close_pending`、`push_braced_statement_block_scope`、`pop_braced_statement_block_scope`、`commit_braced_statement_block_expression`、`commit_braced_statement_block_close`、`emit_braced_statement_separator_missing`、`emit_braced_close_missing`、`emit_braced_close_error` を参照する。

fixture は `braced_statement_block_is_a_primary_with_all_separator_forms`、`braced_statement_block_ast_keeps_statement_count_close_and_range`、`braced_statement_block_is_binding_power_invariant_and_keeps_deeper_newlines_local`、`braced_statement_block_keeps_colon_arguments_and_outer_chain_flat`、`braced_statement_block_recovers_mandatory_slots_and_close`。
