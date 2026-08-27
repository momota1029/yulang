# TypeExpression malformed-newline-owner policy (TMN)

## 1. 状態・正本・改訂台帳

Pattern annotation addendum (16042–16556) が cross-owner problem を定義した。正本の TMN addendum は [parser architecture design](../../../notes/design/2026-08-20-yu-syntax-chasa-architecture.md) の 16557–16860 行で、`TMN-B`、`TMN-P`、`TMN-C`、`TMN-S` から成る。16859–16860 行の closing signature は承認を記録する。positional fence (16862–17289) は TMN semantics ではなく caller-boundary propagation mechanism を置換する。implementation authority は `2c29c0d1`、`d99d49e7`、`72948621`、`13450592`、`bef9cb96`、`57afb683`、`7838355e`、`52429b94`、`a0365f98`。

## 2. 問題・対象範囲・非対象

TMN は non-empty malformed TypeExpression prefix 後の maximal trivia が same required slot の deeper continuation か、enclosing owner へ untouched で返すべきものかを決める。mandatory primary、Path、ArrowRhs、delimited item、forall、NamedRecord、Pattern annotation に統一して適用する。surface TypeExpression grammar、primary/tail precedence、delimiter ownership、public parser option、AST vocabulary は変えない。

## 3. canonical rule と decision procedure

`TMN-B` は recovery entry で base を一度 capture する。

```text
continues_after_newline(trivia, continuation_base) :=
    trivia has physical newline
    and indent after its last physical newline > continuation_base
```

`TMN-P` は implicit default を置かない。

```text
TypeMalformedNewlinePolicy :=
    ContinuationQualified { continuation_base }
  | AnyPhysicalHandoff
```

`TMN-C` は maximal trivia run を priority 順に classify する。physical newline なし、active caller `StopKind::Newline`、any-physical handoff、continuation-qualified boundary、deeper continuation。`TMN-S` は result を保持する。

```text
TypeInvalidRunDisposition :=
    RetryCurrent
  | RetryAfterTrivia(TriviaRun)
  | BoundaryCurrent
  | BoundaryAfterTrivia(TriviaRun)
```

scanner は current owner boundary、hard handoff、current retry candidate、maximal trivia と `TMN-C`、deeper-trivia candidate、次の opaque malformed unit の順で調べる。

## 4. authority・precedence・ownership transfer

active `StopKind::Newline` は indentation/policy より先に勝つ。`BoundaryCurrent` は current byte を untouched にする。`BoundaryAfterTrivia` は malformed prefix だけを emit し、trivia と following boundary を owner に残す。`RetryAfterTrivia` は exact trivia run 一つを same required slot に transfer し、slot が一度 consume/retry する。direct CST でも Error と retried child の間に一度 emit する。outer mandatory Pattern annotation だけが captured Pattern continuation base を渡し、nested type recovery は ordinary active type base に戻る。

## 5. worked trace と byte ownership

以下の authoritative trace は design-doc 16803–16828 行。

| source と design-doc 行 | classification | required byte ownership |
| --- | --- | --- |
| `x: @\n  Int` (16809) | `TMN-DeeperContinuation` then `RetryAfterTrivia` | `@` に一つの `Error(Type::Primary)`。trivia を一度 consume して `Int` が同じ annotation slot を complete |
| `A::@\n  B` (16811) | `TMN-DeeperContinuation` then `RetryAfterTrivia` | Error は `@` を own。`B` は同じ PathSegment を retry |
| `T(@\n  A)` (16813) | `TMN-DeeperContinuation` then `RetryAfterTrivia` | Error は `@` を own。`A` が retry し call owner が `)` を consume |
| `'[@\n  A]` (16818) | `TMN-DeeperContinuation` then `RetryAfterTrivia` | Error は `@` を own。`A` が retry し row owner が `]` を consume |
| `x: @\n  <EOF>` (16820) | `TMN-DeeperContinuation` then `BoundaryAfterTrivia` | Error は `@`。trivia は outer-owned のまま、same-cause Missing は増えない |

## 6. participating parser state と adoption matrix

| state/type | producer | query / consumer | observable effect |
| --- | --- | --- | --- |
| `RequiredTypeRecoveryContext` | mandatory TypeExpression entry | required AST/direct adapter | private outer-role と optional Pattern-base context |
| `TypeMalformedNewlinePolicy` | 各 scanner caller | `classify_type_malformed_trivia` | explicit newline ownership policy |
| `TypeMalformedTriviaClassification` | `classify_type_malformed_trivia` | boundary normalization/scanner | five `TMN-C` outcome を保存 |
| `TypeInvalidRunRecovery` | malformed-run scanner | AST/direct owner adapter | error range と disposition を保持 |
| `TypeInvalidRunDisposition` | `scan_type_item_invalid_run_with_disposition` | required/delimited/forall/Path/NamedRecord recovery | new AST node なしに retry/handoff を決定 |
| `TriviaRun` | state-neutral trivia probe | classifier/disposition | exact raw-trivia ownership |

`pattern.rs` は AST/direct path の両方で `pattern_continuation_base` を capture し、outer annotation の mandatory TypeExpression entry だけで `RequiredTypeRecoveryContext::with_malformed_continuation_base` を使う。

## 7. recovery・cardinality・no-cascade contract

`error_range` は non-empty/contiguous。boundary は punctuation を owner に残し、retry は candidate byte を consume しない。`BoundaryAfterTrivia` は scanner-owned trivia を意味せず、`RetryAfterTrivia` だけが same-slot transfer。したがって `x: @\n  <EOF>`、`T(@\n  )`、active-Equal boundary は `@` だけを Error にし、second Error/cascading Missing を作らない。

## 8. lifecycle・rollback・invariant

continuation base は recovery-slot entry で一度 capture し、following token/EOF から再計算しない。maximal trivia は state-neutral probe。internal NamedRecord colon probe は handoff 前に rollback。AST/direct adapter は retry/transfer 完了まで disposition を保持し、checkpoint state を exact restore する。

## 9. Yulang2 divergence

TMN は every physical newline を raw scanner safe point にせず qualifying/deeper malformed newline を区別する。approved polymorphic-variant any-newline behavior は explicit `AnyPhysicalHandoff` exception のまま。

## 10. known residual・exclusion・extension rule

implicit default はない。future bracket-row grammar は `BracketRowAlignmentPolicy` を保持し silent opt-in しない。future TypeExpression owner は policy/base を宣言し、owner transition まで `TypeInvalidRunDisposition` を保存し、raw-newline shortcut を `TMN-C` に normalize し、retry/caller-boundary handoff の AST/direct fixture を置く。

## 11. 実装・fixture・consumer page cross-reference

core implementation は `parse_required_type_expression_with_recovery_context`、`commit_direct_type_expression_with_recovery_context`、`classify_type_malformed_trivia`、`scan_type_item_invalid_run_with_disposition`、`continues_after_newline`。Pattern integration は `parse_pattern_bp` と `RequiredTypeRecoveryContext::with_malformed_continuation_base`。

fixture は `malformed_trivia_classifier_distinguishes_all_tmn_c_outcomes`、`mandatory_type_recovery_yields_deeper_newlines_to_an_active_owner`、`malformed_delimited_items_retry_after_deeper_trivia`、`malformed_path_segment_retries_after_deeper_trivia`、`malformed_forall_body_retries_after_deeper_trivia`、`malformed_continuation_qualified_slots_pair_raw_and_space_prefixed_newlines`。

consumer summary は [Pattern type annotation](../patterns/type-annotation.md)、[TypeExpression core](../types/type-expression-core.md)、[named-record type](../types/named-record-type.md)、[forall type](../types/forall-type.md)、[effect-row type](../types/effect-row-type.md)。
