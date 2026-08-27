# Standalone TypeExpression core

## 1. 状態・正本・最終確認

Authoritative な standalone TypeExpression core 追補は `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の 12155–12866 行にある。後続の `TMN` newline-owner policy と positional-fence implementation authority は 16557–16861 行と 16862–17289 行で shared recovery を refine するが、TypeExpression を Pattern や `OperatorTable` に依存させない。

core 実装 commit は `b24a3e90`、`3bc6e108`、`c5896444`、`5a375dfd`。recovery follow-up は `d99d49e7`、`72948621`、`42c1544c`、`2c4d7540`。このページは `5df7ace1` を基準に確認した。

## 2. 対象範囲と非対象

core は identifier/sigil/number atom、`::` path、adjacent call、whitespace ML-style application、fixed right-associative arrow、parenthesized/tuple-like group を所有する。これは expression `OperatorChain` variant ではなく、Pattern grammar と並ぶ standalone fixed-precedence grammar owner である。

`for`、named record、polymorphic variant、effect row、bracket row、declaration use-site wiring、typing、HIR/lowering、diagnostics text、formatting は original core scope 外である。exotic primary は後続の Authoritative addendum が別途追加する。

## 3. BNF 相当の grammar

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

`Number` は valid primary だが path segment ではない。qualifying newline は delimited item を区切り、deeper newline は type continuation になる。

## 4. Judge・priority・owner boundary

tail judge は active stop、close、equal-or-shallower caller boundary に先に譲る。leading trivia がないときだけ exact `->`、adjacent `(`、exact `::` を認識する。`type_ml_arg` 内の non-empty trivia は whitespace arrow/path probe より前に nested argument を終了する。その後に trivia-qualified arrow/path と candidate-backed `TypeApplyArgument` を調べる。

従って `List(Int)` は call、`List (Int)` は apply である。`F A::B` の path は applied argument 内、`F A ::B` の path は outer type が所有する。arrow は full RHS を accept して current loop を終え、`A -> B -> C` は right-associative になる。dynamic binding-power table は使わない。

## 5. Byte-exact CST の worked examples

追補には complete CST tree があるが byte-range 付き tree はない。ここでは range を作らない。

```text
List(Int)::Result Arg -> Out -> Final
```

設計文書 12324–12353 行は source-order の `TypeExpression` 一個を示す。`TypeCallTail`、`TypePathTail`、`TypeApplyArgument`、そして RHS に二個目の arrow tail を持つ `TypeArrowTail` である。whitespace は apply/arrow owner に属する。

```text
(A)
```

設計文書 12366–12369 行はこれを one-element grouped type とし、literal trailing separator を持つ `(A,)` と `(A;)` を tuple-like と区別する。

```text
F A -> B
```

設計文書 12488–12500 行はこれを `(F A) -> B` に固定する。対照的に `F A->B` は nested ML argument の arrow 前に trivia がないため `F (A -> B)` になる。

## 6. Parser 側 AST shape

`TypeExpression` は `primary`、ordered `postfix`、optional `arrow`、`range` を持つ。core postfix variant は `TypePostfixTail::{Path, Call, Apply}`。`TypeCallTail` と `ParenthesizedTypeGroup` は recovered element と close slot を持ち、group は grouping/tuple classification 用の literal `trailing_explicit_separator` も持つ。

current `TypePrimary` enum には後続 exotic variant もあるが、core form は `Atom` と `Parenthesized` のままである。`TypeApplyArgument` は accepted trivia `boundary` と boxed argument を own し、arrow は precedence を left-nested AST へ rewrite せず recovered RHS を持つ。

## 7. Typed recovery table

| condition | recovery と continuation |
| --- | --- |
| missing mandatory primary | `TypeRole::Primary` Missing 一件。caller boundary は non-consuming |
| malformed primary の後に valid primary | non-empty Primary Error 一件後 same-slot retry |
| segment のない `::` | `TypeRole::PathSegment` Missing 一件。boundary は owner のまま |
| malformed path segment | PathSegment Error 一件。numeric segment は accept しない |
| missing call/group item または separator | typed item/separator Missing 一件後 same-position retry |
| accepted call/group の missing close | closing-delimiter Missing 一件。別 form に reinterpret しない |
| `->` の missing/malformed RHS | `TypeRole::ArrowRhs` Missing/Error 一件。outer boundary は non-consuming |
| apply trivia 後に primary なし | apply authority も synthetic Missing もなし |

全 scanner は active stop、close、delimiter、separator、qualifying newline、valid retry candidate の前で止まる。`TMN-C` と positional fence は malformed newline-bearing trivia でも no-cascade を保つ。

## 8. Boundary と state-restoration contract

candidate probe は sink-free かつ state-neutral。accepted call/group は delimiter、stop、layout base、`TypeDelimitedOwner` を同期し、apply は `type_ml_arg` だけを push する。normal/recovery/rollback exit は TypeExpression episode と positional-fence state を含めて復元する。AST/direct は同じ candidate、layout、cut、safe-point decision を共有する。

## 9. Yulang2 divergences

Yulang3 は fixed tail、ML scope behavior、right-associative arrow を保つが、empty `Separator` node の代わりに literal newline trivia を使う。generic `InvalidToken` recovery は typed Missing/Error と owner-safe boundary に置換する。numeric path segment を除外し、generic wrapper を避け、one-site outer missing-role override を提供する。

## 10. Known residual / deferred surface

missing nested delimiter の背後にある hidden caller-boundary case は、後続 `ASOB-G` と Cast work が characterization しており、黙って正常化しない。core が deferred にした exotic primary と declaration/pattern use-site integration は別の Authoritative addendum が所有する。

## 11. 実装と regression fixture の cross-reference

`crates/yu-syntax/src/grammar/type_expr.rs` では `parse_type_expression`、`parse_required_type_expression_with_recovery_context`、`commit_direct_type_expression`、`commit_direct_type_expression_with_recovery_context`、`parse_type_call_tail`、`parse_parenthesized_type_group`、`parse_type_arrow_tail`、`commit_direct_type_delimited`、`classify_type_malformed_trivia`、`scan_type_item_invalid_run_with_disposition` を参照する。

fixture は `type_core_forms_keep_fixed_flat_structure`、`type_arrow_is_right_associative_without_an_operator_table`、`type_call_and_group_accept_comma_and_semicolon`、`type_groups_reuse_layout_boundaries_without_synthetic_separator_nodes`、`type_apply_uses_one_argument_per_nonempty_trivia_boundary`、`path_and_arrow_missing_rhs_leave_an_outer_layout_newline_unconsumed`、`type_call_missing_item_and_close_keep_distinct_typed_slots`。
