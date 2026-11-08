# §5.5b 注釈追加監査（9列正規化）

新spec integration 3fdd6c3acac223b0920730979b3fd01b94366509、旧実機 d4c8bc8fc8a49173180932cd25921a2c41057354。原ログ・raw scheme・unit全文は runtime-cycle-2-annotations.md。新規実行なし。

`一致` は備考の局所範囲のみ。dump exit0 は診断を伴う場合があり受理を意味しない。timeout 124 は runner が割り当てた値。

| ID | 出典 | 規則 | 例 | 実機結果 | 新spec | Lean | 分類 | 備考 |
|---|---|---|---|---|---|---|---|---|
| ANN-01 | 旧 web/docs/ja/reference/type-theory.md:163–165; effects.md:236–237 | 結果の具体注釈は本体の既知の禁止 effect を拒否する | quick-direct-body: `f():[ping]int=pong::get()` | check1: effect filter mismatch: pong is not allowed by [ping] | 05 §5.5b 第1項 | AnnotationFinalization.Examples.completed_body_effect_rejected | 一致 | この最小例での一致。source 一般の完全性ではない。 |
| ANN-02 | 旧 type-theory.md:163–165; constraints/machine/bounds.rs:3213–3254 | 引数の注釈で既知の具体 effect も検査する | quick-known-callback: `apply(g:()->[pong]int):[ping]int=g()` | check1: pong is not allowed by [ping] | 05 §5.5b 第2項 | AnnotationFinalization.known_forbidden_at_finalization / forced_forbidden_at_finalization | 一致 | この最小例での一致。Lean は有限事実モデル。 |
| ANN-03 | 旧 type-theory.md:163–165; compact/finalize.rs:837 | 一般化後の未知 effect の具体化は元注釈を再検査しない | quick-late-unknown: `apply(g):[ping]int=g()`、later が pong callback を渡す | check0。apply raw scheme quantifiers ['16]、effect Var('16)、later:[pong]。late-use-runtime run0:7 | 05 §5.5b 第4項 | CommonEffectAnnotations.Frozen.later_instantiation; AnnotationFinalization.later_instantiation; AnnotationSnapshots.instantiation_keeps_observation | 一致 | 具体的な一般化＋後続具体化を確認。複数型で呼べることだけを一般化の根拠にはしていない。 |
| ANN-04 | 旧 type-theory.md:151–165 | glob callback 注釈でも後から具体化された effect は元 filter で拒否されない | quick-late-glob: `apply(g:()->[_]int):[ping]int=g()`、later pong | check0。apply/later 表示は ANN-03 と同形 | 05 §5.5 と §5.5b 第4項 | CommonEffectAnnotations.Frozen.later_instantiation | 一致 | 具体例の一致。完成済み snapshot が前提であり、glob 全境界意味論の検証ではない。 |
| ANN-05 | 旧 type-theory.md:163–165; 今回 scc-peer 4試験 | SCC peer 由来の具体 effect を検査し、宣言順交換で受理が変わらない | `f():[ping]int=g()` / `g()={f; pong::get()}`、両順と ping 対照 | pong 両順 check1 同 filter 診断。ping 両順 check0。dump 両 member [pong]/[ping] | 05 §5.5b 第3項 | AnnotationFinalization.scc_member_order | 一致 | 4具体ソース比較。f→g 呼出、g→f 値参照の依存循環で、SCC内部IDはinstrumentしていない。Lean は解決済み識別子を保持する member permutation。両方向実呼出は ANN-06。 |
| ANN-06 | 今回 scc-forward/reverse、scc-short、scc-pure 試験 | effectful な両方向実呼出 SCC の順序不変 | `f(x):[ping]int=g x` と g の pong/再帰分岐。短縮版 `g()={pong::get();f()}` | 通常4入力の check/dump 各40秒で打切り。短縮2入力は各5秒。純粋 `f()=g();g()=f()` は check0/dump never | 05 §5.5b | AnnotationFinalization.scc_member_order | 未確認 | timeout は拒否・不一致・無限ループの証明ではない。原因未特定。有限 Horn 定理は旧 solver の終了性を主張しない。 |
| ANN-07 | 今回 quick-nested-known / quick-nested-late 試験 | 入れ子 binding の既知 effect は拒否、外側一般化後の未知 effect は許す | 既知: inner 本体 pong。未知: `outer(g)={my inner():[ping]int=g();inner()}`、later pong | 既知 check1。未知 check0、outer/generalized later に pong | 05 §5.5b 第5項 | AnnotationFinalization.Examples.nested_binding_finishes_its_own_unit | 未確認 | 個別の受理・拒否は仕様と整合する。しかし inner と outer の推論完了時刻を分離して観測できていないため、第5項の時点規則の一致認定はしない。 |
| ANN-08 | 今回 nested-later-known / nested-known-before 試験 | inner 完了後の外側制約で注釈を再検査しないという時点 | `outer(g)={my inner():[ping]int=g();g as (()->[pong]int);inner()}` | check1。outer 引数を最初から [pong] とする対照も check1 | 05 §5.5b 第5項 | AnnotationFinalization.Examples.outer_effect_does_not_recheck_finished_inner | 未確認 | ソース順だけで inner が finalize 済みだったとは断定できない。捕獲 g の非一般化共有変数と後続制約が関わる。新仕様との不一致とは断言しない。Lean は完成済み innerHistory と別の outer 事実の比較。 |
| ANN-09 | 旧 type-theory.md:163–165; constraints/machine/bounds.rs:3174–3212,3272付近; propagate.rs:42 | filter は静的検査であり保存する solver weight から除く | check_and_erase_*、lower_filters 別表、constrain_new_lower_bound_by_registered_filters | ソース読取。既知/後続 lower を別表で検査し weight から filter を除く | 05 §5.5 / §5.5b | CommonEffectAnnotations.Frozen.emit | 一致 | 文書と狭い実装読取の一致。旧 solver は一般化直前の一回検査ではなく増分検査なので、観測意味の同値は別途必要。 |
| ANN-10 | 旧 compact/finalize.rs:837; compact/tests/case_02.rs:53; constraints/tests/case_02.rs:6930 | scheme 向け compact finalize は filter を持ち越さない | finalize_drops_filter_only_stack_weights_on_negative_vars; neg_stack_filter_is_checked_but_not_stored_as_right_weight | cargo test 各1件 PASS / exit0。runtime-cycle-2-annotations.md | 05 §5.5b 第4項 | CommonEffectAnnotations.Frozen.emit_subst / Frozen.later_instantiation | 一致 | 二つの狭い unit と ANN-03 の実例で支持。任意の一般化経路の完全証明ではない。 |
| ANN-11 | 新 lean/Yulang/AnnotationFinalization.lean 冒頭; CommonEffectAnnotations.lean 冒頭 | Lean の SCC 順序定理と構造推論/source 全体の対応 | 有限 Horn facts の全 member 収集→least solve→freeze | 旧 source との機械検証済み翻訳は今回未確認。新規実機試験なし | 05 §5.5b | AnnotationFinalization.scc_member_order; CommonEffectAnnotations の completed-boundary 留保 | 未確認 | 構造推論から有限 facts への翻訳は明示入力。source/SCC の完成境界への到達は定理の主張外。この制限を source 全体の PROVED や仕様の欠落と読み替えない。 |

## 有用な最小入力

```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my apply(g): [ping] int = g()
my later() = apply (\() -> pong::get())
```

これは check 0。apply 自身の完成時点ではeffectが未知、scheme内で量化されている。後から `pong` を渡せる。対照として `g: () -> [pong] int` をapplyの宣言に入れると check 1。

```yulang
my f(): [ping] int = g()
my g() = { f; pong::get() }
```

これは宣言順を逆にしても check 1。g の f 参照は呼出でないが、関数間依存は循環している。`pong` を `ping` に替えると両順 check 0。

## 検証範囲

Leanは読取のみ。Lean全体ビルド/verifyなし。旧Rust unitを2個実行、両PASS/exit0（全ログruntime-cycle-2-annotations.md）。リポジトリ編集・公開なし。時間制限は監査runnerが各CLIへ設定した40秒または5秒であり、このジョブ全体のプラットフォーム上限ではない。打切りexit124はrunnerが割り当てた値で、旧CLI自身が返した値ではない。
