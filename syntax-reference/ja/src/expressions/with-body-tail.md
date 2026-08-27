# `WithBodyTail`

## 1. 状態・正本・最終確認

Authoritative な generic-expression `WithBodyTail` 追補は `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の 10662–11085 行にある。operator-chain / colon-application が予約していた terminal tail の slot を具体化する追補であり、declaration companion の追補とは別である。

approval / implementation commit は `72922125` と `5ca66006`。後続の canonical `Statement` 拡張は shared consumer infrastructure であり、第二の `WithBodyTail` grammar ではない。

## 2. 対象範囲と非対象

この grammar は operand-complete `OperatorChain` 後の terminal generic-expression continuation を追加する。body は inline の一つの canonical `Statement`、または non-empty で strictly-indented な statement block である。body は nested canonical statement なので、その内部では ordinary nested operator tail、colon application、別の `WithBodyTail` を使える。

`struct`、`enum`、`type`などの declaration companion は定義しない。`with { ... }` もこの generic form ではない。companion/module semantics、receiver attachment、cleanup の意味、target association、HIR/lowering、inference、diagnostics prose、formatting も対象外である。

## 3. BNF 相当の grammar

```text
WithBodyContinuation :=
    ChainContinuingTrivia WithBodyTail

WithBodyTail :=
    WithKw WithIntroducerTrivia Colon WithBody

WithIntroducerTrivia := G*

WithBody :=
    InlineWithBody
  | IndentedStatementBlock

InlineWithBody :=
    G0* Statement [ Semicolon ]
```

`with` は exact maximal word であり、`withx` と `with?` は split しない。required lone `:` に `::` を split しない。introducer は keyword と colon の間に newline を含む maximal trivia を許す。`ChainContinuingTrivia` は outer chain が所有し、post-keyword / inline post-colon trivia は tail が所有する。

## 4. Judge・priority・owner boundary

operand-complete site では active owner stop、matching delimiter、equal-or-shallower newline が先に各 owner へ返る。`StopKind::With` が inactive のとき、exact `with` probe は dynamic LED、fixed postfix、ML argument、colon application より先である。word を accept した後は tail が mandatory colon/body recovery を所有し、identifier、dynamic operator、ML argument へ rollback しない。

`WithBodyTail` は `TerminalOuterTail` である。target child を持たず current outer chain を finish する。nested body は fresh statement/chain を所有するため、`a with: b: c` と `a with: b with: c` は inner terminal continuation を body に置き、outer `a` chain へ second terminal sibling を足さない。後続 fixed tail には parenthesize などで new outer chain が必要になる。

## 5. Byte-exact CST の worked examples

追補は source-order CST tree を持つが byte-range 付き tree はない。ここでは range を作らない。

```text
a + b with: cleanup
```

設計文書 10769–10783 行は complete tree を示す。outer `OperatorChain` が `a`、`+`、`b` を所有し、後続の `WithBodyTail` が `WithKw`、colon、post-colon trivia、`cleanup` を持つ nested `Statement` / `OperatorChain` を所有する。

```text
value with: body
```

設計文書 10962 行は complete inline-body recovery-table row を記録する。`WithBodyTail` 一つ、complete colon slot、complete inline `Statement`、diagnostic なしである。

```text
a with: b: c
```

設計文書 10988–10996 行は nested ownership を固定する。`WithBodyTail` は outer-tail syntax であり、body statement の nested `OperatorChain` が `b` とその `ColonApplicationTail` を所有する。

```text
f with: body
```

設計文書 11002–11004 行は ML application より exact `with` が優先することを固定する。これは target segment が `f` の with-tail であり、`Primary(f), MlArgument(with), ColonApplicationTail(body)` ではない。

documented indented complete form は設計文書 10963 行の `value with:\n  body` である。inline wrapper ではなく opening trivia と nested statement を含む一つの `IndentedStatementBlock` を持つ。

## 6. Parser 側 AST shape

この grammar 範囲の `TerminalOuterTail` は正確に `ColonApplication(ColonApplicationTail)` と `WithBody(WithBodyTail)` variant を持つ。`WithBodyTail` は正確に `keyword: WordSpan<'source>`、`colon: Recovered<Range<usize>>`、`body: Recovered<WithBody<'source>>`、`range: Range<usize>` を持つ。

`WithBody` は正確に `Inline { statement: Box<Statement<'source>> }` と `Indented { block: IndentedStatementBlock<'source> }` variant を持つ。target field、numeric binding-power field、inline-semicolon field、trivia field はない。これらは CST/source ownership に残る。`colon` と `body` を別 recovered slot にすることで、missing-colon retry と colon がある body-missing case を区別する。

## 7. Typed recovery table

| condition | recovery と continuation |
| --- | --- |
| EOF の `value with` | `WithKw` を保持し、zero-width `Missing(Introducer: Colon)` 一件だけ。body Missing を cascade させない |
| `value with body` | zero-width introducer-colon Missing 一件後、同じ position を inline statement body として retry |
| `value with :: body` | `::` を split しない。colon Missing 後も longer punctuation を body / outer recovery へ残す |
| EOF の `value with:` | colon を保持し zero-width `Missing(Body: Statement)` 一件 |
| indent `<= with_base` の post-colon newline | body Missing 一件。newline と following token は outer statement owner へ残す |
| deeper newline 後の EOF | `IndentedStatementBlock` と opening trivia を保持し `Missing(IndentedStatement)` 一件 |
| `value with: ;` | body Missing 一件と literal terminal semicolon を保持 |
| valid body 前の malformed non-statement run | maximal non-empty `Error(Body)` 一件後、同じ body slot を retry |
| malformed inner indented statement / nested tail | nested/shared owner へ委譲し duplicate With recovery を出さない |

`Missing` は zero-width、`Error` は maximal かつ non-empty であり、committed recovery node 一つは diagnostic identity 一つを持つ。comma、matching close、dedent、equal-or-shallower newline、active owner stop、EOF、valid retry point は scanner boundary に残る。

## 8. Boundary と state-restoration contract

tail は introducer/layout episode 前に active indentation baseline を snapshot する。physical post-colon newline がなければ canonical inline `Statement` を一つだけ選び、newline があれば following indent が strictly deeper のときだけ indented block を選ぶ。inline terminal semicolon は tail が一回だけ所有し、その後の trivia と outer boundary は tail 外に残す。

AST / direct-CST path は normal、recovery、rollback の全 exit で input、line state、sink、ambient-owner scope、stop set、indentation state、`ml_arg`、その他の local parser frame を restore する。nested body recovery は outer comma、matching close、dedent、owner boundary を caller へ残す。

## 9. Yulang2 divergences

Yulang3 は Yulang2 の `WithBlock` を `WithBodyTail` へ改名し、flat-chain の terminal role を明示する。empty/generic invalid-token recovery を typed `WithBodyRole` Missing/Error と same-position missing-colon body retry に置き換える。単一の Yulang2 `Lex` emission を再現せず、trivia を nearest typed CST owner へ分ける。

original Yulang3 slice は Yulang2 declaration-companion / brace path を意図的に除外し、shared canonical `Statement` expansion 前は body 内で当時の statement subset だけを受理した。generic tail は target から declaration companion owner を推測しない。

## 10. Known residual / deferred surface

shared `ASOB-G` caller-boundary residual は隠さず characterization のままにする。missing nested delimited owner の背後にある caller boundary は、その nested owner の recovery scan から見えないことがある。この page はその cross-cutting residual を広げも解決もしない。

declaration companion / brace companion body、companion item classification、name resolution/visibility、receiver / method attachment、cleanup/local-module interpretation、HIR/lowering、inference、diagnostics wording、formatting は deferred surface である。

## 11. 実装と regression fixture の cross-reference

`crates/yu-syntax/src/grammar/expression.rs` では `recognize_with_body_tail`、`parse_with_body_tail`、`parse_with_inline_statement`、`commit_with_body_tail`、`with_body_absent_boundary`、`with_body_error_retry`、`emit_with_missing`、`emit_with_error` を参照する。

fixture は `with_body_tail_is_terminal_and_reuses_inline_and_indented_statement_bodies`、`with_body_tail_missing_colon_is_single_typed_recovery_and_retries_body`、`indented_and_with_inline_ambient_scopes_restore_after_ast_and_direct_episodes`。
