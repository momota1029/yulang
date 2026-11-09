# Cycle50: residual source preservation and continuation

## 基点・部分目標
予定開始 2026-11-09T19:27:19Z、終了期限 19:52:19Z。前cycle49の公開復旧と書込み終了を待ち、remote `328ad7eed717e13303c0d24ee7c329c7dba594a1` と完了心拍を再取得した。19:29:19Zに時刻を記録してfetch開始。`integration/m1-final` は `1a3dc217d799e24034dae319fd58c9208d36df6f`。standing orders、inbox I-12まで、heartbeat、cycle49、関連規則を再読。状態ACTIVE、STOPなし。前回復旧は完了済みで今回の復旧は不要。

integration取り込みではcycle49報告と心拍だけが競合。監督統合版は復旧中の古い記録、ローカル版はその後の検証済み完了追記だったため、コードは統合版のまま、より新しい完了記録を重ねてmerge commit `e8383bd22` にした。作業場は既存の一つだけ、他の書込み担当の完了確認後に開始。

**部分目標は閉じた。** 有限str/equality断片で、未解決の条件付き要求を正確に残し、飽和atomsとの組が独立source意味論の全モデルを保存することを証明した。さらに、既に導いた事実と保留要求だけを残した入力へ新しいstr制約を加えて再実行すると、元の全要求から再構築した場合と全モデル・実checked判定が一致することを証明した。cycle49の「atomsだけでは条件が落ちる」反例を修復する、1つの部分目標である。

## データと量化
全定理は任意の有限source table T、seed slot列S、slot等式列L、名前付き要求列Rを量化する。空table、重複source名、cycle、未到達slotを除外しない。slot i,j はTの位置。割当a,bは全slotをCommonの型とeffect行へ送る。追加制約Eは任意のstr seed slot列。

Packetは既存の飽和Stateと保留slot対列の組。Modelsはatomsのモデルかつ各保留対の「receiverがstrならtargetもstr」という条件。SourceModelはcycle49の独立定義を変更せず使用する。生のbuildは表現済みslotだけを扱い、外側runが既存のmissing checkで欠けた名前を報告する。報告はadapterの診断であり、言語のrejectedではない。

## 新規定理22本
`CommonRoleDynamicIndexResidualSource`（14本）:
- `pairs_exact`（補助）: 任意i,j、列挙された対への所属 iff そのsource名の要求がRにある。
- `residual_exact`（健全性・完全性）: 任意i,j、残った対 iff 名前付き要求かつiが独立導出で未到達。
- `residual_checked_exact`（健全性・完全性）: 任意i,j、残った対 iff 名前付き要求かつ実checkedProduceIndexがnone。
- `build_models_exact`（健全性・完全性）: 任意a、PacketのModels iff SourceModel。全モデル集合の一致であり、str帰結だけの一致ではない。
- `run_ok_iff`（健全性・完全性）: 任意packet、実runのok packet iff 全endpointが存在しpacket=build。
- `run_success_iff`（健全性・完全性）: okの存在 iff scope。外部の充足性前提なし。
- `run_models_exact`（健全性・完全性）: 任意の成功packetとa、Models iff SourceModel。
- `run_has_model`（健全性・非空性）: 任意の成功packetを、具体的な全str・空effect割当が満たす。
- `run_covers_requests`（完全性・補助）: 任意成功packetとR内の要求r、rに対応するslot対が存在し、保留列にあるか実checked呼出しがsomeを返す。要求を捨てない。
- `model_order_independent`（健全性・完全性）: 同じ要求所属を持つ任意のleft/right列で、全aについてPacketモデルが一致。列そのものの順序一致は主張しない。
- `atom_only_loss_repaired`（境界回帰）: cycle49でatomsだけを満たす非SourceModel割当は、今回のPacketモデルではない。
- `residual_unseeded`（回帰）: [10,20]、seedなし、10→20で保留対は[(0,1)]。
- `residual_chain_closed`（回帰）: [10,10,20,30]、seed0、10→20→30は別occurrenceを含め全て解消。
- `dangling_names_reported`（回帰）: 欠けたendpointは既存missing列の順・重複を保ったerrorになる。

`CommonRoleDynamicIndexResidualResume`（8本）:
- `pending_names_exact`（健全性・完全性）: 任意i,j、保留対をsource名へ戻した要求所属 iff 元の保留対所属。alias occurrenceの一部だけを誤って復活させない。
- `pending_names_scoped`（補助）: 保留名は常に表現済みendpointを持つ。
- `retained_source_exact`（健全性・完全性）: 任意a、S・旧飽和事実・Eと保留要求だけのSourceModel iff S++Eと元の全要求RのSourceModel。既解消要求のtargetは保存済み事実なので要求を再保持する必要がない。
- `resume_models_exact`（健全性・完全性）: 任意a、保留から継続したPacketモデル iff 元の全問題にEを加えて再構築したPacketモデル。
- `resume_checked_exact`（健全性・完全性）: 任意i,j、継続後の実checked呼出しがsomeを返すoutが存在 iff 全再構築SourceModelがiをstrに強制。
- `resume_pending_exact`（健全性・完全性）: 任意i,j、継続後の実checked呼出しがnone iff 全再構築SourceModelの中にiで非同値な二つのモデルがある。
- `resume_empty_models`（意味的閉包）: E=[]の継続は全Packetモデルを保存。atoms列同一とは主張しない。
- `delayed_chain_reactivates`（回帰）: 全て保留だった10→20→30に後からseed0を入れると保留列が空になり、下流の実checked呼出しも成功。

主型性の新しい主張はない。許されない範囲を新しい言語仕様として決めたのではなく、有限正str・構成済みseed/equality状態・追加str制約への限定である。docstringで明記。既存Lean定理は変更していない。両モジュールをYulangへimport、全22定理をAuditへ登録。

## 検証
コマンド `cd lean && ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build --wfail Yulang.CommonRoleDynamicIndexResidualSource`、終了0:
```text
✔ [286/286] Built Yulang.CommonRoleDynamicIndexResidualSource (1.4s)
Build completed successfully (286 jobs).
```

コマンド `cd lean && ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build --wfail Yulang.CommonRoleDynamicIndexResidualResume`、終了0:
```text
✔ [287/287] Built Yulang.CommonRoleDynamicIndexResidualResume (1.2s)
Build completed successfully (287 jobs).
```

コマンド `cd lean && ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 /tmp/cycle50-audit.lean`、終了0:
```text
'Yulang.CommonRoleDynamicIndexResidualSource.pairs_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualSource.residual_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualSource.residual_checked_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualSource.build_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualSource.run_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualSource.run_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualSource.run_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualSource.run_has_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualSource.run_covers_requests' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualSource.model_order_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualSource.atom_only_loss_repaired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualSource.residual_unseeded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualSource.residual_chain_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualSource.dangling_names_reported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualResume.pending_names_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualResume.pending_names_scoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualResume.retained_source_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualResume.resume_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualResume.resume_checked_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualResume.resume_pending_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualResume.resume_empty_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualResume.delayed_chain_reactivates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

コマンド `bash tools/verify-lean.sh . origin/integration/m1-final --no-build`、終了0:
```text
verify-lean: . @ 93df7ecb4 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

全22定理の公理はpropext / Classical.choice / Quot.soundのみ。最初のfocused試行は関数適用の構文一箇所で失敗し、明示引数へ修正後、上記最終コードの全対象検証が成功。`git diff --check` 終了0。

全体lake build、全Audit、全体公理gateは指示どおり未実行。監督役の全体検証を待つ。小さなbuild・auditのみを上限180秒の継続セッションで実行し、未完の重い処理はない。

## Yulang2との照合
最新work/dots-auditのx-oracle X13〜X17、spec/06-roles.md 6.3の関連型等式・安定までの保留・兄弟の連言を参照。旧実機の例はこのstr/equality carrierの完全性の検証ではない。新たなYulang2実機試験は未実施。意味論の選択は加えておらず、質問ノート追加なし。

## 残りと次の候補
一般B4へ残る橋は5本: source_boundary_adequate、generated_work_closed、saturate_terminates_and_closes、saturated_frontier_exact、resolve_dictionary_order_sound。今回の結果で一般形の本数を減らさない。未接続は一般payload、任意初期State、parser/lowering、四分類、辞書同値、主型性。既存診断Endpoint.evalもint-onlyのまま。

次の候補: (1) strを保持するsource endpointと診断treeの接続、(2) この残余付きモデル契約を一般生成childの領域・停止性へ接続、(3) 追加str seedだけでなく、追加slot等式による保留再活性化へ拡張。
継続adapterは元の入力から保存事実を再計算する定義であり、永続cacheや計算量改善・実runtime高速化を主張しない。

## 公開・時間・容量
ローカル実装commit `aec504980`、`93df7ecb4`。開始heartbeat公開commit `d181e116d54e269a2f88b922bbe41b536779bfdc`。
個別blob作成とSHAだけのtree、非force・expected-head指定で、`work/dots-main`だけへ公開する。integration基点からの全差分10ファイルを対象に、公開後にblob SHAを照合する。内容入り一括treeは使わない。
この記録時点は公開準備中。公開commitと読戻し結果は確認後に追記する。開始・検証時の空きはいずれも48GB。使用量の枠は不明。
