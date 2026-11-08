# §5.5b 追加監査: 注釈 filter / SCC / 具体化

対象: integration 3fdd6c3acac223b0920730979b3fd01b94366509、新 spec 05 §5.5b、旧 Y2 d4c8bc8fc8a49173180932cd25921a2c41057354。2026-11-08 UTC。cycle-1 `Y2-EFF-011` は境界部品だけを照合し source/SCC 完全性を留保していた。本追試もその留保を一括解除しない。

各例は no-prelude、ローカル `act ping/pong`、`our get: () -> int` を利用。入力と全出力は runtime-cycle-2-annotations.md、機械可読結果は results.jsonl。check と dump のみが大半で、再帰例の実行 run はしていない。`dump` は診断があっても exit 0 なので、受理は check で判定。

| ID | 一つの主張 | 旧実機/文書/実装 | 新 spec/Lean | 判定と限界 |
|---|---|---|---|---|
| ANN-01 | 結果の具体注釈は本体の既知の禁止 effect を拒否する | quick-direct-body `f():[ping]int=pong::get()` check1 `effect filter mismatch: pong is not allowed by [ping]` | 05 §5.5b第1項。AnnotationFinalization.Examples.completed_body_effect_rejected | この最小例は一致。source一般の完全性ではない |
| ANN-02 | 引数の注釈で既知の具体 effect も検査される | quick-known-callback `apply(g:()->[pong]int):[ping]int=g()` check1 同診断 | §5.5b第2項。known_forbidden_at_finalization / forced_forbidden_at_finalization は有限事実モデル | この最小例は一致 |
| ANN-03 | 一般化後の未知 effect の具体化は元注釈を再検査しない | quick-late-unknown `apply(g):[ping]int=g()`、later が pong callback を渡す。check0。raw の apply scheme は quantifiers ['16]、effect row Var('16)、later は `[pong]`。late-use-runtime は外側 handler で run0 7 | §5.5b第4項。CommonEffectAnnotations.Frozen.later_instantiation / AnnotationFinalization.later_instantiation / AnnotationSnapshots.instantiation_keeps_observation | この具体的な一般化＋後続具体化は一致。単に2型で使えたことを一般化根拠にしていない |
| ANN-04 | glob callback 注釈でも後から具体化された effect は元filterで拒否されない | quick-late-glob `apply(g:()->[_]int):[ping]int=g()`、later pong が check0、apply/later表示はANN-03と同形 | §5.5b第4項と5.5 glob。Frozen.later_instantiation は完成済みsnapshot仮定 | 一致する具体例。globの全境界意味論の検証ではない |
| ANN-05 | SCCのpeer由来の具体effectを注釈で検査し、宣言順交換で受理が変わらない | scc-peer-forward/reverse: `f():[ping]int=g()` / `g()={f; pong::get()}`。両check1同診断。ping対照は両check0。f→g呼出、g→f値参照の循環。dump両member [pong]/[ping] | §5.5b第3項。AnnotationFinalization.scc_member_order は member list permutation の一般定理、各 member は同じ解決済み識別子を保持 | 4つの具体ソース比較は一致。SCC内部IDをinstrumentしていない。値参照による依存循環であり、両方向の実呼出をする再帰はANN-06 |
| ANN-06 | effectfulな両方向実呼出SCCで順序不変を確認できるか | scc-forward/reverseと許可ping版はcheck/dump各40秒で打切り。より小さなscc-short-forward/reverseも各5秒打切り。純粋 `f()=g();g()=f()` はcheck0/dump never | §5.5b、scc_member_order。有限Horn定理はこの旧solverの終了性を主張しない | 未確認。timeoutを拒否判定/不一致/無限ループの証明とはしない。ホスト資源、終了性の原因特定なし |
| ANN-07 | 入れ子bindingの既知effectは拒否、外側一般化後の未知effectは許す | quick-nested-knownはcheck1、quick-nested-lateはcheck0でouter/generalized laterにpong | §5.5b第5項。AnnotationFinalization.Examples.nested_binding_finishes_its_own_unit | これらは整合するが、innerとouterの正確な推論完了時刻の分離を示す十分な実験ではない |
| ANN-08 | inner完了後の外側制約を再検査しない、という時点そのもの | nested-later-known: `outer(g)={my inner():[ping]int=g(); g as (()->[pong]int); inner()}` はcheck1。outer引数最初から[pong]版もcheck1 | §5.5b第5項、Examples.outer_effect_does_not_recheck_finished_inner は完成済みinnerHistoryと別のouter事実の比較 | 未確認/候補。ソース順だけでinnerが実際にfinalize済みだったと断定できず、捕獲gの非一般化共有変数と後続制約が関わる。仕様不一致と断言しない |
| ANN-09 | filterは静的検査であり保存するsolver weightから除く | 旧type-theory.md:163–165。bounds.rs:3174–3212 check_and_erase_*、lower_filters別表への登録、:3272付近 constrain_new_lower_bound_by_registered_filtersで後続lower検査。propagate.rs:42も検査後filterをAllにする | §5.5/5.5b。Frozen.emit はcheck trueならformula、falseならbot | 文書と狭い実装読取は一致。ただし旧solverは検査を一般化直前に一度だけ呼ぶ実装ではなく、filter表で増分検査する。観測意味の同値を別途要する |
| ANN-10 | scheme向けcompact finalizeではfilterを持ち越さない | compact/finalize.rs:837 principal_stack_weightはfilterをAllに。既存unit finalize_drops_filter_only_stack_weights_on_negative_vars PASS。neg_stack_filter_is_checked_but_not_stored_as_right_weightもPASS | Frozen.emit_subst / later_instantiation | 二つの狭いunitとANN-03の実例で支持。任意の一般化経路の完全証明ではない |
| ANN-11 | LeanのSCC順序定理は構造推論/source全体を検証しているか | 旧sourceとの機械検証済み翻訳は今回なし | AnnotationFinalization冒頭:有限Horn facts、全member収集、least solve、freeze。structural inferenceからfactsへの翻訳は入力。CommonEffectAnnotations冒頭もcompleted boundaryへの到達を主張しない | いいえ。この制限をsource/SCC全体のPROVEDに読み替えない |

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
