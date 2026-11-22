# Yulang dot 第343周: 現行版の where 子を、親から辞書までつなぐ

- 開始時の `integration/m1-final`: `fe6dec78ea45ece8475638eb6aa42c69c3b49365`。常設指示、inbox と spec 6.3/6.5・型推論の核、C342 完了版 `ba075649afbd9db0e898f138d4aaa2fffb3fcc0b` を取得した。I-62 に従い、旧 `Local` との対応は作業対象外。最新の証人つき分類と、実際の solver 側の観測・位置・出力を区別した。
- 検証対象の固定コミット: `959454542c7bfc1ae0d4c1ac6e234f4375656e27`。証明は、既存の隔離版 C319 の取引に対するもので、元の raw 実行器を変更していない。

## 今回確かめたこと

1. **親の根拠は、最終状態の真理でなく実の入力にある。** `InitialRoot343.anchored/source_backed/root_election`。同じフィクスチャの初期に記述した `Foo(width,width)` ラベル、型付け済みの閉じた項、正規化済みの nominal 翻訳、別に記述済みの width 制約と元の slot 名 2 から、実際の親行 `0 ↦ Foo(2,2)` の source 支持を得た。C342 で条件だった一行 view の支持がこのフィクスチャでは成立する。任意の完了集合に依存せず親の二捕捉を実 packet と同じ名前で読む。一般の Rust パーサーや初期正規化の証明ではない。
2. **通常 compiler の唯一の子の名は具体的に決まる。** `LogicalChild343.batch/port_zero`、`Ordinary343.actual`。任意の保護名リストについて、実際の通常 compiler はこの親から一つの compound 子を出し、その下端・中心・上端の名前は新規の連続した三つ。親の出力 target は 4 のまま。単一の入力 span でも、通常側の下端/上端の型名は集約で並べ直される。中心の 2 と同一名と仮定せず、`InitialModels343.first_values` で、実際に書いた二つの集約等式から型の意味が等しいと示した。
3. **通常 compiler の新名と現在の物理端点を、同じ割当で照合した。** `FreshModel343.fixed_output_model`、`FreshValues343.mode_match`、`Placement343.kept_model/actual_place`。任意の実 C319 版つき最終モデルから、全既存 journal 名と固定 target 4 を保持する拡張が存在する。元の current 下端、独立に記録された center、再利用された上端をそれぞれのモードの式から読み、実 compiler の別の論理名と一致させる。その割当で真になる三行の alias だけを追加する。既存名を新しい形で上書きしたり、物理 target を変えたりしていない。古い子は ID・中心・上端がたまたま同じでも代用できない（`CurrentHistory343.cannot_substitute`）。
4. **最新版の証人付き分類まで、親子を同じモデルで閉じた。** `CurrentOrigins343.recorded/no_promotion`、`CurrentRoot343.rule`、`CurrentChild343.rule`、`OrderedProjection343.projected`。任意の実 C319 最終モデルについて全 journal の名前を保った一つの割当があり、その割当で取引後の版つき raw 再帰木、通常 compiler が指定する順序の子、親子両方の実配置、最新の証人つき `Classify`、同じ全辞書の宣言的 `Evidence` がそろう。親の入力は source、子の行は実際に完了済みの**現行親の出力**。alias 自体は根拠に昇格しない。親の literal output 4 と、実版つき行順（所有者の出力、新 lower、再利用 upper）を保持する。`CurrentHistory343.nonvacuous` は実モデルからこの結論が実在することも検証した。
5. **由来が別々に必要なことを対照で確認した。** 普通の式・制約、実配置をそのままにした反事実で、完了済み出力の権限だけを外すと、親の局所提案は同じ通常 compiler 子を返すが、その子を選ぶ証人がない（`OriginSplit343.independent`）。逆に、初期 source 支持だけを外すとその子の局所証人は残るが、親は選べない（`ReceiptSplit343.independent`）。正規化後の通常の真理を支持に取り違えていない。これは新しい solver の実行や pending verdict の主張ではない。
6. **再利用できる橋。** `ModeBridge343.with_actual_site` は任意の実登録 site と普通の view について、役割と順序付き固定出力が文字通り一致し、各位置の三モードの意味が同じモデルで一致するなら、同じ割当のまま三行ずつの alias で `Placement` を作る。`no_fresh_origin` はその追加で新しい支持行が生じないと示す。`RankedBridge343.preserves_rank` は各対応名の rank 一致を**別に**確認した場合だけ既存 K2 証明を保つ。C319 の具体的な合成がこの一般橋と一致することも `BridgeInstance343.exact_join/models_by_generic_bridge/ranked_by_generic_bridge` で照合した。

## どこまでか・次

- **(4) 残り1群。** 証人付き分類から同じモデルの辞書への既存の定理は使用済み。I‑61 の承認された任意の nested／compound source について、真に非点の支持つき端点から、開閉両方の厳密な残差・捕捉・順序付き出力の一般 producer は残る。I‑58 の実中心等式と I‑59 の K2 は変更していない。C319 の現行子は物理名は違うが意味はこの例では同じであり、任意非点用の結果ではない。
- **(2) 残り2群。** ① 一般の実成功停止で、source origin・本当にコミットした where の宣言/位置/版/mode と、現在の full packet・固定出力を独立に作る producer。今回閉じたのは隔離版 C319 の親子。元の C316 は実到達停止と旧 selected 表示を持つが、元の full packet producer が不可能である事実は残る（`StoppedObstruction341.actual_obstruction`）。元の環境を直したとは言わない。② 実成功停止が返した診断の全枝・順序と最新 witness の辞書を一般に照合する。今回の `OrderedProjection343.ordered_places` は実親子の一例。次は実 source/commit producer からこれを運ぶ。停止性・全実行器・Rust 動作／全 Lean build は未検証。
- [次の具体的な証明の切り方](../design/dots-cycle-343-next-raw-producer.md)。言語仕様を変えず、質問ノートは作っていない。使用量の枠は不明。

## 検証

- 起動時は executor が offline。許可された同じ managed cloud に再接続し、前回の公式 Lean 4.35.0 と焦点を絞ったキャッシュを再使用した。 `lake build --wfail` は新規モジュールを指定。普通の Lean compiler の小さい独立実行も検証した。実需要と等しいリテラル入力で保護リストを変えると、子の三名は (13,14,15) から (20,21,22) へ移り、出力 target は 4 のまま。raw/Rust の実行ではない。
- 不変 proof commit を別 detached worktree へ取得し、変更パス全体の blob と旧 barrel の元バイト列からの import 追記のみを照合。I-57 の凍結2ファイルは Git blob ID のみ確認し、内容は読まず展開もしなかった。凍結を除外した `verify-lean.sh --no-build`、`git diff --check`、新規 Lean source と独立 audit の `lean --trust=0 -DwarningAsError=true` を実行。24 新規 source、5 独立 audit（公理を表示した定理48件）、scope の公理チェック 102716 宣言、すべて PASS。標準許可は propext、Classical.choice、Quot.sound のみ。旧 barrel は 321951 byte をそのまま保ち、実 import 24件のみ追加。
- `notes/verification/cycle343/` に検証結果と diff 検査全文。公開先は `work/dots-main` のみ。固定 checkpoint: `c49f5be34d5464493b0ea67ddd5c9b92744ea600`（初期根拠）、`e99d1d046f981d6d0d858be6f1d36308f8cb9d36`（実 compiler 子配置）、`af51b2441996c8f30cefc47e00ecb33a626239c3`（同一割当）、`12db8a20465e1fb8a465c32d96855676019ebf1c`（支持の対照と一般橋）。
- 実作業開始 10:33:58 UTC／最終公開開始 11:23:59 UTC。proof 時点は38変更パス。最終ログ・報告を含め 45 パスを照合する。

### 新規定理名（`lean/Yulang/`）
- `GeneralDeclarativeBridgeInstance343`: current_demand,exact_join,matching_levels,bare_rank,ranked_by_generic_bridge,models_by_generic_bridge
- `GeneralDeclarativeCurrentChild343`: interval,child_actual,heads,choice,rule
- `GeneralDeclarativeCurrentClosure343`: resolves,summarizes,selected,dictionary,current_place,one_model
- `GeneralDeclarativeCurrentHistory343`: cannot_substitute,nonvacuous
- `GeneralDeclarativeCurrentOrigins343`: completed,recorded,nominal_origin,emitted_origin,no_promotion
- `GeneralDeclarativeCurrentRoot343`: traced,choice,rule
- `GeneralDeclarativeCurrentWorld343`: grows,regular,new_lo,new_hi,root_low,member_atom,member_interval,member_row,new_constraints,added_bound,current_rank,child_compile,stays
- `GeneralDeclarativeFrameGuard343`: flat,compound,ranked
- `GeneralDeclarativeFrameRank343`: level_low,level_high,old_below,low_not_old,level_lo,level_mid,level_hi,ordinary_layout,before_fresh,logical_levels,level_root,level2_here,levelL0,levelH0,levelL1,levelH1,ordinary_edge,bound_levels
- `GeneralDeclarativeFrameShape343`: retained_constraints,exact_intervals,exact_rows,source_ordinary,output_ordinary,grows
- `GeneralDeclarativeFreshModel343`: names_survive,cap_bounds,built_model,fixed_output_model
- `GeneralDeclarativeFreshValues343`: present,printed,exact_values,mode_match
- `GeneralDeclarativeInitialModels343`: parts,first_capture,second_capture,ranges,equal_uses,kept_stage,singleton_bounds,first_values
- `GeneralDeclarativeInitialRoot343`: anchored,origin_unique,source_backed,root_election,exact_inputs
- `GeneralDeclarativeLogicalChild343`: center,translated,jobs_eq,port_zero,batch
- `GeneralDeclarativeModeBridge343`: pointwise,written,recovered,source_iff,realized,with_actual_site,no_fresh_origin
- `GeneralDeclarativeOrderedProjection343`: root_registered,root_place,ordered_places,exact_targets,projected
- `GeneralDeclarativeOrdinary343`: empty,inputs,where_rows,emits,actual
- `GeneralDeclarativeOriginSplit343`: still_observed,traced,root_still_elected,independent
- `GeneralDeclarativePlacement343`: fresh_lower,avoids_history,aliases_valid,kept_model,read_aliases,actual_place
- `GeneralDeclarativeRankedBridge343`: directed,whole,preserves_rank
- `GeneralDeclarativeReceiptSplit343`: present,present_current,observed,heads,choice,independent
- `GeneralDeclarativeWithheldInput343`: only_receipts,not_variable,never_root,isolated,no_anchor,not_ready,no_authored_no_root
- `GeneralDeclarativeWithheldReceipt343`: only_source,below0,above0,lower_source,center_source,upper_source,terms_no_zero,bound_isolated,isolated,not_anchored,not_ready,cannot_use_truth_to_select
