# Call / field / path / ML-application tail

## 1. 状態・正本・最終確認

Authoritative な Call/Field/Path/ML fixed-tail 追補は `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の 9695–10182 行にある。current ML-delimited-owner composition は、Call/Index/Projection item が共有する typed expression-delimited owner を定めた後続 Authoritative Index/Projection 追補 10184–10660 行で refine されている。

implementation series は `82bd7613`、`4d2931d6`、`97b6bc81`。後続 shared-owner wiring は `5f067e33`、current ambient boundary handling は `a355058d` と `af3cce2f` が扱う。

## 2. 対象範囲と非対象

本ページは target-free source-order `OperatorChain` continuation 四種、adjacent CallTail、FieldTail、PathTail、one-argument-per-node ML application を扱う。Call は layout-aware argument list、Field は adjacent dot/name、Path は `::` + normal/sigil segment、ML は qualifying non-empty trivia + nested chain 一つを所有する。

Index/Projection body/recovery は後続の固有 addendum、Colon application、`WithBodyTail`、semantic call/field/path resolution、application association、HIR lowering、inference、diagnostics wording、formatting は対象外である。

## 3. BNF 相当の grammar

```text
FixedPostfixContinuation := CallTail | FieldTail | PathTail

CallTail := LParen CallOpeningTrivia
            [ OperatorChain { CallSeparator OperatorChain } [ CallSeparator ] ]
            RParen
CallSeparator := Comma | Semicolon | ImplicitNewlineBoundary(call_base)

FieldTail := Dot Identifier
PathTail := ColonColon G* PathSegment
PathSegment := Identifier | SigilIdentifier

MlApplicationContinuation := MlArgumentSeparator MlArgument
MlArgumentSeparator := non-empty trivia with no newline
                     | newline with following_indent > active_base
MlArgument := OperatorChain under the ml_arg stop scope
```

Call opener と Field dot/name は adjacent、Path は `::` 後の trivia を許す。ML は qualifying non-empty separator と shared NUD candidate の両方を要する。equal-or-shallower newline は ML separator でなく outer owner へ返る。

## 4. Judge・priority・owner boundary

operand-complete site では active owner stop、matching close、equal-or-shallower newline が先に勝つ。次に canonical longest dynamic judge が accepted suffix/infix spelling を保持する。続いて adjacent `(` は CallTail、exact `.identifier` は FieldTail、exact `::` は PathTail、projection lookahead は bare Field recovery より先に判定する。qualifying trivia + shared NUD のときだけ `MlArgument` を作る。

ゆえに `f(x)` は CallTail、`f (x)` は parenthesized argument を持つ ML application となる。ML は own layout frame を push せず、nested chain だけが `ml_arg` を立てて current typed baseline/owner を読む。later qualifying trivia は enclosing chain が sibling ML argument として claim する。四 continuation は terminal `ColonApplicationTail` より前にあり、colon は current chain を終える。

## 5. Byte-exact CST の worked examples

追補は source-order CST shape を示すが byte-range 付き tree はない。ここでは range を作らない。

```text
f(x)
```

設計文書 9929 行は adjacent opener を `CallTail` 一つとして固定する。

```text
f (x)
```

設計文書 9930 行は non-empty same-line trivia + parenthesized NUD を CallTail でなく `MlArgument` 一つとして固定する。

```text
f x y
```

設計文書 9978、10152 行は sibling `MlArgument` 二つを固定する。`y` 前の space は nested first argument ではなく outer chain が所有する。

```text
a.b(c)::d e
```

設計文書 10101–10110 行は primary `a`、FieldTail、CallTail、PathTail、trivia、MlArgument の source-order outline を与える。target child を tail 内へ nest しない。

## 6. Parser 側 AST shape

`OperatorChainItem::FixedPostfix` は `FixedPostfixTail` を持ち、`OperatorChainItem::MlArgument` は正確に boxed `argument` と `range` を持つ。本ページの `FixedPostfixTail` variant は `Call`、`Field`、`Path` である。

`CallTail` は正確に `open`、ordered `arguments`、recovered `close`、`range` を持つ。`FieldTail` は正確に `dot`、recovered `name`、`range` を持つ。`PathTail` は正確に `separator`、recovered `segment`、`range` を持ち、`PathSegment` は正確に `Identifier` または `SigilIdentifier` である。separator spelling/trivia や target edge は AST に持たない。

## 7. Typed recovery table

| condition | recovery と continuation |
| --- | --- |
| `f()` | valid empty call。recovery なし |
| `f(,a)` / `f(a,,b)` | absent argument ごとに zero-width CallArgument Missing 一件。separator を保持して retry |
| EOF/caller boundary の `f(a` | argument を保持し boundary を非消費、missing `RParen` 一件 |
| valid NUD 前の malformed call argument | maximal non-empty Error 一件後 same-slot retry |
| EOF/owner boundary の `x.` | dot を保持し zero-width FieldName Missing 一件 |
| `x..`、`x...`、`x.(`、`x.{` | longer operator/projection candidate を Field + Missing へ split しない |
| EOF/owner boundary の `x::` | `::` を保持し zero-width PathSegment Missing 一件 |
| `x::::name` | first segment Missing 後、second `::` で non-consuming same-position retry |
| EOF または shared NUD なしの `f ` | empty ML node を commit しない |
| accepted ML prefix/nullfix の operand 欠落 | nested OperatorChain が operand Missing 一件を所有し、ML は duplicate しない |

Missing は zero-width、Error は non-empty、accepted introducer は cut、owner boundary は非消費である。

## 8. Boundary と state-restoration contract

Call は Parenthesis、comma/semicolon/right-parenthesis stop、indentation baseline、`ExpressionDelimitedOwner::Call` を push し、normal/recovery/rollback exit で全て restore する。ML は enclosing typed owner または root context を読むが、nested `ml_arg` scope を exact restore する。nested delimiter frame、active ambient owner claim、lexical region、outer close、equal-or-shallower newline は高い priority の boundary に残る。

## 9. Yulang2 divergences

Yulang3 は Yulang2 composite `DotField` を Dot + Identifier へ split し、separator wrapper/empty implicit-separator node でなく raw call punctuation/trivia を emit し、typed zero-width Missing/maximal Error recovery を使う。ML は Yulang2 trivia-free ML candidate を一般化せず strict whitespace/layout separator を維持する。

## 10. Known residual / deferred surface

documented `ASOB-G` caller-boundary residual は hidden にせず characterize する。Index/Projection syntax body、semantic target association、resolution、HIR lowering、inference、diagnostics、formatting は deferred または固有 grammar owner の責務である。

## 11. 実装と regression fixture の cross-reference

`crates/yu-syntax/src/grammar/expression.rs` では `recognize_fixed_postfix`、`recognize_ml_argument`、`ml_argument_candidate_input`、`ml_argument_context_allows`、`parse_fixed_postfix_tail`、`parse_call_tail`、`call_argument_error_retry_ast`、`commit_fixed_postfix_tail`、`commit_call_tail`、`commit_call_separator`、`emit_call_missing`、`emit_call_close_missing`、`emit_call_error` を参照する。

fixture は `fixed_field_and_path_tails_are_flat_and_bp_neutral`、`call_tail_uses_adjacent_opener_and_layout_boundaries`、`call_tail_recovers_missing_arguments_and_closing_delimiter`、`call_and_ml_adjacency_keep_flat_source_order`、`ml_arguments_split_on_trivia_but_keep_adjacent_fixed_tails_and_colon_terminality`、`call_and_ml_recovery_keep_owner_boundaries_local`、`call_tail_restores_each_enclosing_owner_frame`。
