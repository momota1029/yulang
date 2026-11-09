# Cycle45: checked named-source entrance

開始 2026-11-09T16:57:38Z。基点integration d9a2142f2。前回cycle44のcompleted心拍・報告を確認、未公開コードなし。統合時の報告/心拍競合は監督版優先で解消。開始空き49GB。

## 部分目標
不在のsource endpointを持つ要求を黙って捨てず、正確な診断リストを返すchecked入口を閉じた。既存の任意有限table・名前付きrequest listに対して、計算したcoverageと独立WellScopedが同値。全成功出力は既存adapter outputに一致する。これはadapter入力整形式の検査で、言語rejected分類ではない。意味論変更なし。

## 定理（全量化と前提）
namespace Yulang.CommonRoleDynamicIndexCheckedSource。tableは任意有限Nat列、requests/errorsは任意名前対列、s/outはState table.length、aは全slotへのComp Common.model割当。
- present_exact [健全性/完全性]: 全table,nameでpresent=true iff nameを持つslotが存在。
- covered_exact [健全性/完全性]: 全table,要求rでcovered=true iff 両端の名前を持つslot i,jが存在。
- missing_exact [健全性/完全性]: 全table,requests,rで診断への所属 iff 要求に属し、両端slotが存在しない。
- missing_nil_iff [健全性/完全性]: 全table,requestsで診断が空 iff WellScoped。
- run_ok_iff [健全性/完全性]: 全table,s,requests,outでrun=ok out iff WellScopedかつoutは既存adapter output。
- run_error_iff [健全性/完全性]: 全table,s,requests,errorsでrun=error errors iff WellScopedでなくerrorsが全missing要求リスト。
- error_nonempty [補助]: 全入力でrun=error errorsならerrorsは非空。
- success_coverage [完全性]: run=ok outを前提に、全r∈requestsで対応slotと生成辺が存在。
- success_models [健全性/完全性]: run=ok outの下、任意aでoutのモデル iff sのモデルかつsource identity整合かつextend sからDerivedな全slotの型がstrと意味同値。
- success_executes [条件付き健全性]: run=ok outかつaがoutのモデルなら、既存の実producer/alias/seed混合Executed証人が閉包に存在。モデル存在は結論しない。
- error_members [健全性/完全性]: run=error errorsの下、任意rの診断所属 iff 要求に属し両端slotが存在しない。
- scope_membership_invariant [補助]: 任意left,rightで全rの所属が同値なら、scope成功が同値。順序/重複への不変性。診断リスト自体は順序と重複を保持。
- scope_example_valid / scope_example_missing / malformed_run [回帰]: 名前表[10,10,20,30]の連鎖がscopeを通る。表[10,10]に不在名20,30を含む要求は全件（重複を含む）診断される。後者は任意初期State 2でerrorを返す。

## 検証
focused: `cd lean && ELAN_HOME=../../elan ../../elan/bin/lake build Yulang.CommonRoleDynamicIndexCheckedSource --wfail` exit0、281 jobs。
audit: `lake env lean --trust=0 /tmp/Cycle45Audit.lean` exit0、今回15定理。標準三公理のみ。
全体build、全Audit、verify-lean.shは最新指示により未実行。全体PASSとはしない。

### focused出力全文
```text
✔ [281/281] Built Yulang.CommonRoleDynamicIndexCheckedSource (982ms)
Build completed successfully (281 jobs).
```
### audit出力全文
```text
'Yulang.CommonRoleDynamicIndexCheckedSource.present_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexCheckedSource.covered_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexCheckedSource.missing_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexCheckedSource.missing_nil_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexCheckedSource.run_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexCheckedSource.run_error_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexCheckedSource.error_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexCheckedSource.success_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexCheckedSource.success_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexCheckedSource.success_executes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexCheckedSource.error_members' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexCheckedSource.scope_membership_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexCheckedSource.scope_example_valid' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexCheckedSource.scope_example_missing' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexCheckedSource.malformed_run' depends on axioms: [propext, Quot.sound]
```

## 未達
B4主定理の残り5橋は変わらない: source_boundary_adequate / generated_work_closed / saturate_terminates_and_closes / saturated_frontier_exact / resolve_dictionary_order_sound。
今回のsource入口は既存の名前表/要求リストを入力する。parser loweringではない。str断片のみ。入力scope成功は実行の成功や整合性の存在、全要求解決を保証しない。一般B4・四方向分類・主型性は未達。
次の候補: (1) 実source構文の名前表/要求抽出とscope検査への意味保存、(2) str以外のchecked宣言への有限領域拡張、(3) 最終整合性の構成または矛盾検査との統合。

## Yulang2照合
最新audit枝fetchは自動審査が停止済み監査のscope外と判断して拒否。迂回せず、既存origin/work/dots-auditのx-oracle X13〜X17を読んだ。新実機照合なし。本追加は内部入力のcoverage診断で言語エラー分類ではない。spec6.3のsource共有と衝突する意味論は導入しない。

## 制限・公開
初回proofのsimp/tactic参照エラーを修正し再build/audit済み。開始心拍updatedを未来時刻で手入力した誤りを直ちに実時計から訂正。以降は時計取得。環境中断なし。利用枠は不明。成果・報告・心拍を7ファイルとして個別blob→SHA tree→非force expected-head更新で一括公開し、取得した全treeをローカルと照合する。検証後の新規コード変更なし。

報告準備時刻: 2026-11-09T17:02:06Z。

## 公開照合
2026-11-09T17:05:44Z、成果commit a96f61b6ae3e903055833017418c15861d4081b5 をfetchし、git diff --exit-code HEAD FETCH_HEADは差分空・exit0、working tree clean。7ファイルの全tree一致とcompleted心拍を読戻し確認。開始から約8分。途中公開失敗なし。
