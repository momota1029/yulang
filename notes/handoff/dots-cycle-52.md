# Cycle52: exact original-source residual frontier

## 基点・復旧・部分目標
予定開始 2026-11-09T20:27:19Z、期限 20:52:19Z。準備の shell 時刻は 20:26:43Z、
開始後の確認は 20:27:32Z。integration/m1-final の基点は
`c6b0fee4a9285754c9472f1e158d7daf86e26b59`、開始前の公開枝は
`091b0a7686213617ca40919e32fea322892cc988`。
standing orders と inbox I-12 までを再読し、ACTIVE・STOP なし。
cycle51 は完了心拍と報告が揃い、復旧は不要。既存の唯一の作業場・キャッシュを再利用した。
統合の競合は前回報告と心拍だけで、公開済みの新しい完了記録を保持し、
`220a51158` に統合を記録。開始心拍を `03545978fbf69b3fb279817fb44a1cb53726e8e7` で公開。

**部分目標は閉じた。** 任意の有限更新バッチを逐次圧縮して実行した最終 pending は、
元入力の全要求を残した全再計算の pending と、slot-pair の順序も含めて同じリストになる。
保留の各要素は「元要求に所属し、元入力の全独立モデルが receiver を str に強制しない」
ことと同値。二つの非同値なモデル、実 checked の失敗、成功入口の全要求の保持も接続した。
cycle51 の checked の失敗だけの特徴付けから、実 pending リストそのものへ橋を閉じた。

## 定義・量化・範囲
新規 `CommonRoleDynamicIndexResidualFrontier` だけで証明を追加した。
既存の実行定義・Lean 定理は変更せず、実行コードの wrapper も追加していない。
任意の有限 table T、初期 Problem P、有限 update 列 U、slot i,j、型・効果割当 a を量化。
独立意味論は既存 SourceModel、実行版は既存 solve/run/build/checkedProduceIndex。
空 table、重複 source 名、循環要求、到達しない slot を排除しない。
主定理には充足可能性・acyclicity・閉包の oracle を仮定しない。
run の定理では、通常どおり `run = ok packet` だけを入口の前提に置く。
補助の unknown 不変条件だけは、具体的な source model と非 str receiver を前提にする。

対象は固定有限 carrier、正 str seed、slot 型等式、与えられた有限更新列。
これらは実装・証明断片の限定で、仕様上の拒否条件ではないと docstring に明記した。
型成分だけを制約し、効果成分は自由。source の同名 slot は別々の pair のまま保持する。
重複した named request の列要素は、既存 pairs の列挙で重複しない。
リスト同一性は内部 pending だけ。ordinary atoms・辞書・一般の診断 tree は同一としない。

## 14 定理と M1 のどの側か
すべて `Yulang.CommonRoleDynamicIndexResidualFrontier` に属する。
- `compact_requests_unknown`（健全性・完全性、補助）: 任意 P,a,i,j、a が P のモデルで i が非 str なら、表現された i,j の元要求所属 iff compact 後の要求所属。
- `appendMany_requests`（補助）: 任意 P,U,r、元全連結の要求所属 iff P または U 内のある更新に所属。
- `advanceMany_requests_unknown`（健全性・完全性、補助）: 任意 P,U,a,i,j、a が元全入力のモデルで i が非 str なら、最終圧縮要求所属 iff 元要求所属。
- `solve_residual_exact`（健全性・完全性、本部分目標）: 任意 T,P,U,i,j、pending 所属 iff 元要求所属かつ元全入力が i を str に強制しない。
- `solve_pending_countermodels`（健全性・完全性）: 同じ量化で、pending 所属 iff 元要求所属かつ i の型が非同値な二つの元 source model が存在。
- `solve_residual_checked`（健全性・完全性）: 同じ量化で、pending 所属 iff 元要求所属かつ実 checked の返値が none。
- `run_residual_exact`（健全性・完全性、入口）: 任意成功 run と i,j について、返された packet の pending 所属が元入力の独立 forcing と同値。
- `run_covers_original_requests`（健全性・完全性、要求保持）: 任意成功 run と元要求 r について、対応する slot i,j が存在し、pending に残るか実 checked が成功する。
- `update_order_pending`（健全性・完全性、順序独立）: 任意 P と同じ更新所属を持つ有限 left/right、i,j について、pending 所属が同値。
- `residual_ext`（補助）: 任意 P,Q、全 slot pair の residual 所属が同値なら、共通の正準列挙による residual リストが等しい。
- `solve_pending_rebuild`（健全性・完全性、本部分目標）: 任意 T,P,U、最終 solve の pending リスト = 元入力を全連結して build した pending リスト。
- `update_order_pending_list`（健全性・完全性、順序独立）: 同じ更新所属を持つ有限 left/right の pending リスト全体が等しい。
- `run_pending_rebuild`（健全性・完全性、入口）: 任意成功 run の pending リスト = 元入力の全再計算の pending リスト。
- `aliased_cycle_frontier`（回帰）: 5 slot、10 の alias と 30/40 の循環を含む具体例で、解決済み alias の要求は消え、未解決循環の二つの pair だけが残る。後着 seed で残りが空になる。

主型性の新結果はない。新しい言語意味論や、分類・辞書の設計判断もしていない。

## 検証
コマンド `cd lean && ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build --wfail Yulang.CommonRoleDynamicIndexResidualFrontier`、終了コード 0:
```text
✔ [289/289] Built Yulang.CommonRoleDynamicIndexResidualFrontier (1.4s)
Build completed successfully (289 jobs).
```

コマンド `cd lean && ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 /tmp/cycle52-audit.lean`、終了コード 0:
```text
'Yulang.CommonRoleDynamicIndexResidualFrontier.compact_requests_unknown' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualFrontier.appendMany_requests' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualFrontier.advanceMany_requests_unknown' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualFrontier.solve_residual_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualFrontier.solve_pending_countermodels' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualFrontier.solve_residual_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualFrontier.run_residual_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualFrontier.run_covers_original_requests' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualFrontier.update_order_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualFrontier.residual_ext' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualFrontier.solve_pending_rebuild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualFrontier.update_order_pending_list' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualFrontier.run_pending_rebuild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualFrontier.aliased_cycle_frontier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

コマンド `bash tools/verify-lean.sh . origin/integration/m1-final --no-build`、終了コード 0:
```text
verify-lean: . @ 075085dbd (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

全 14 定理を Audit に登録し、Yulang import も追加した。公理は
propext / Classical.choice / Quot.sound のみ。`git diff --check` も終了 0。
初回の証明では未導入の否定量化子補題・tactic を使って失敗したため、
標準の Classical.byContradiction に置き換えた。cases 後の等式と未使用 simp 引数も修正し、
最終コードで focused build と trust-0 audit を再実行した。
開始直後の shell background 起動は存続しなかったため、結果を成功とはせず、
実行 session に切り替えた。最終のビルドは 1.4 秒で終了し、未完了の重い処理はない。
全体 lake build・全 Audit・全体公理 gate は、指示どおり未実行。監督役の全体検証を待つ。

## Yulang2 との照合
最新 work/dots-audit の notes/audit/x-oracle.md の X13〜X17、および
spec/06-roles.md 6.3 の等式流入・兄弟の安定待ち・連言としての順序独立を読んだ。
旧実機の有限例は、この内部の任意有限 carrier の一般結果の oracle ではない。
新しい Yulang2 実機実行はしていない。意味論の選択が不要だったため質問ノートは追加していない。

## B4 の残りと次の候補
一般 B4 の残りは 5 本のまま:
source_boundary_adequate、generated_work_closed、saturate_terminates_and_closes、
saturated_frontier_exact、resolve_dictionary_order_sound。
今回閉じたのは固定有限 str/equality 断片の元要求からの residual frontier。
一般の source lowering、動的 child の領域拡張、任意制約、四分類、辞書同値は未接続。

次の候補:
1. str を保持する source endpoint と既存の未完成診断 tree を接続し、元要求の provenance を保持する。
2. 実生成 child の source 領域へ固定 slot table の閉包契約を接続する。
3. この断片の exact frontier を B4Target の具体 source instance へ対応させ、一般化に必要な前提を列挙する。

## 公開・容量・時間
実装 commit `075085dbd`。GitHub app の個別 blob と SHA のみの tree を使用し、
非 force・expected-head 指定で work/dots-main だけに公開する。
統合基点からの全差分は 9 ファイル（cycle51 の検証済み完了追記も保持）。
この段階は公開前。公開 commit と tree の全体一致、各 blob の読戻しは確認後に追記する。
開始・検証時の空きは 48GB。worktree の増設・キャッシュ複製・削除はしていない。
使用量の枠は不明。25 分上限内で、時間を埋めるだけの補題を追加せず終える。
