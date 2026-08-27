# TypeExpression malformed caller-boundary positional fence

## 1. 状態・正本・改訂台帳

正本の positional-fence addendum は [parser architecture design](../../../notes/design/2026-08-20-yu-syntax-chasa-architecture.md) の 16862–17289 行。`TMN-C`/`TMN-S` semantics を保ち、以前の recursive `caller_owned_boundary` propagation mechanism を置換する。17291–17399 行の comparison appendix は rollback-and-return-`None` を採用しない理由を記録する。implementation authority は `27620be3`、`42c1544c`、`d58181df`、`3535e237`、`0aabef67`、`7210cd8a`、`de9a0f2f`、`19fc6cfd`、`648f8883`、`4f40022a`、`a090ad35`、`2c4d7540`。

## 2. 問題・対象範囲・非対象

TMN が malformed newline trivia の handoff を決め、positional fence はその caller-ownership fact を every success/recovery return に bool を thread せず arbitrary nesting を越えて残す。これは rollback-owned `ParseLocal` state であり、grammar rule、public parser option、AST field、CST field、新しい `StopKind`、Pattern-specific scanner ではない。

## 3. canonical rule と decision procedure

ambient value は conceptually 次だけ。

```rust
TypeMalformedCallerBoundaryFence { trivia_start: usize }
type_malformed_caller_boundary: Option<TypeMalformedCallerBoundaryFence>
```

committed `TMN-CallerBoundary` で scanner は exact untouched trivia start へ rollback し fence を mark して既存 boundary disposition を返す。consumer は最初に current cursor と `trivia_start` を比較し、一致時だけ maximal trivia を state-neutrally probe して physical newline と active `StopKind::Newline` を確認する。guard は trivia/boundary を consume せず yield する。stack は不要で later mark が inert な earlier position を置換する。

producer は raw-newline/horizontal-prefix trivia を same-line predicate より前に full `TMN-C` へ送る。mark するのは `CallerBoundary` だけで、`Handoff`、`Boundary`、`DeeperContinuation` は mark しない。

## 4. authority・precedence・ownership transfer

exact-position fence は delimiter/stop judge の代替でなく provenance。cursor が start と一致する間だけ TypeExpression の trivia-consumption、owner-classifier、close-slot decision point で勝つ。outer grammar が untouched run と following boundary を own する。accepted かつ unclosed な delimited construct instance はそれぞれ自分の zero-width missing close を一度 emit し、shallow/deep owner の close cardinality を失わない。

## 5. worked trace と byte ownership

| source と design-doc 行 | fence effect | required ownership |
| --- | --- | --- |
| `T((@ \n  A))` (16999, 17189) | descendant `TMN-CallerBoundary` が trivia start を mark | inner/outer accepted parenthesized instance が各々 missing close。一方 newline と `A` は caller-owned |
| `A::@ \n  B` (16981, 17209) | full classifier が same-line Path predicate より先。caller-boundary mark なし | `RetryAfterTrivia(run)` が `B` を retry。space-prefixed run は short-circuit しない |
| `{@ \n  a:A}` (17222) | shallow record fence が close drive へ届く | RecordField Error 一つと NamedRecord missing close 一つ。run は untouched |
| `T(A\n  B)` (16995, 17232) | normal active-newline layout は fence を作らない | ordinary local sequence/layout をそのまま処理 |

これは source/recovery trace。正本は mechanism 全体の byte-range CST tree を出していない。

## 6. participating parser state と adoption matrix

| state/type | producer | query / consumer | phase | observable effect |
| --- | --- | --- | --- | --- |
| `TypeMalformedCallerBoundaryFence` | `mark_type_malformed_caller_boundary` | pending guard | committed caller-boundary trivia start | cursor-scoped provenance のみ |
| `ParseLocal` | parse session creation | scanner/owner adapter | optional fence を保持 | AST/CST field なし |
| `ParseLocalCheckpoint` | `ParseLocal::checkpoint` | `ParseLocal::rollback` | speculative parse | exact optional fence を restore |
| `StopSet` と `StopKind` | caller grammar | pending guard | active newline confirmation | ordinary multiline layout の false positive を防ぐ |
| `TypeMalformedTriviaClassification` | `classify_type_malformed_trivia` | scanner producer | `TMN-C` result | caller-boundary classification だけが mark |
| `TypeInvalidRunDisposition` | malformed scanner | AST/direct recovery | mark 後の handoff | existing recovery result のまま |

production implementation は `session.rs` と `type_expr.rs` に集中し、`declaration.rs` は fence mechanism 本体ではなく restoration/composition を exercise する。

## 7. recovery・cardinality・no-cascade contract

fence は malformed Error を erase せず range も変えない。pending fence は TypeExpression の consumption、classifier advance、close-token consumption を止め、その後 accepted/unclosed delimiter owner ごとに own close slot の Missing を一つだけ emit する。boundary trivia/token は caller に untouched で残る。一 instance の duplicate Missing は禁止するが、distinct nested instance は意図的に deduplicate しない。

## 8. lifecycle・rollback・invariant

`ParseLocal::new` は `None`。checkpoint は option を copy し rollback が restore する。normal hot path は false の `Option`/cursor comparison 一回だけで trivia を rescan しない。fence-hit は state-neutral probe するが fence を clear しない。`trivia_start` を越えて cursor が進めば automatic に inert になり、speculative rollback は speculative mark を消す。

## 9. Yulang2 divergence

これは surface-language change でなく implementation authority。approved TMN recovery ownership を deep nesting でも保ち、return-value propagation gap を避けることが observable consequence。

## 10. known residual・exclusion・extension rule

newline が caller-owned かの判断は TMN の責務。normal multiline construct が false positive になるため generic active-newline guard として使わない。appendix は bare `None`/cut を alternative から除く。committed Error ownership を失うか、recursive success path を通る open-ended typed signal が再び必要になるから。

future TypeExpression recovery owner は committed `TMN-CallerBoundary` だけを mark し、named trivia/close を consume 前に shared pending guard を呼び、per-instance close cardinality を守り、normal/recovery/rollback fixture を追加する。

## 11. 実装・fixture・consumer page cross-reference

core function は `mark_type_malformed_caller_boundary`、`type_malformed_caller_boundary_pending`、`debug_assert_type_malformed_caller_boundary_not_skipped`、`classify_type_malformed_trivia`、`scan_type_item_invalid_run_with_disposition`。session coverage は `checkpoint_restores_type_malformed_caller_boundary_fence`。type fixture は `nested_caller_boundary_stops_outer_normal_item_trivia_consumption`、`delimited_recovery_classifier_yields_to_a_pending_fence_before_trivia`、`legacy_after_trivia_marks_a_caller_boundary_fence`、`malformed_record_name_speculation_rolls_back_a_caller_boundary_fence`、`nested_caller_boundary_realizes_each_unclosed_delimiter_once`、`ordinary_multiline_type_constructs_do_not_create_caller_boundary_fences`。

consumer summary は [Pattern type annotation](../patterns/type-annotation.md)、[TypeExpression core](../types/type-expression-core.md)、[named-record type](../types/named-record-type.md)、[forall type](../types/forall-type.md)、[effect-row type](../types/effect-row-type.md)、[bare nominal type](../statements/bare-nominal-type.md)、[struct declaration](../statements/struct-declaration.md)、[impl shell](../statements/impl-shell.md)、[cast declaration](../statements/cast-declaration.md)。
