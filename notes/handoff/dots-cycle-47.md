# dots cycle47: explicit slot equality feedback
開始: 2026-11-09T17:58:19Z。検証・報告準備終了: 2026-11-09T18:04:22Z。
基点 integration/m1-final: 04bab02e32428b63bb4e548e0d8d0d262c4d94f8。前回cycle46のcompleted心拍・報告を確認し、STOPなし・並行書き込みなしで開始。サイクル数上限なし。今回25分以内という実行指示を優先。

## 部分目標
明示slot型等式を双方向の証拠伝播辺にする有限str Index adapterを追加。旧adapterでは等式原子があってもreceiverがpendingだった具体例が、新adapterでは実checked producerで成功する。設計ノートをコードより先に作成。新たな意味論判断なし、質問ノートなし。

## 全定理と主張
名前空間 `Yulang.CommonRoleDynamicIndexEqualitySource`。以下、一般定理のtableは任意の有限source識別子リスト、seedsはそのslotの任意の有限リスト、linksはslot対の任意の有限リスト、requestsは名前付きIndex要求の任意の有限リスト。非循環性、名前の一意性、外部最終モデルの存在は仮定しない。
1. edges_exact: 任意slot i,jについて辺所属 iff 同一sourceまたは名前付き要求辺またはlinksのいずれかの向きの所属。
2. derived_exact: 任意slot iについて既存closureの導出 iff seed・alias・双方向等式・Indexの独立Derived。
3. saturate_exact: 任意slot iについて計算閉包への所属 iff Derived。
4. initial_models: 任意割当aについて初期全原子成立 iff 全seedがstr同値、全linkの型が同値、source表に関してCoherent。effect等式を新たに要求しない。
5. output_models: 任意割当aについて出力全原子成立 iff 初期全原子成立かつ全Derived slotの型がstr同値。これは全初期モデルの保存ではなく、強化されたモデルの特徴付け。
6. output_has_model: 全str・空effectの具体的割当が出力の全原子を満たす。追加前提なし。
7. equality_models: 任意slotリストxs、i,j、割当aについて、(i,j)または(j,i)がlinksに属しiがxsに属するなら、jを記録したStateの全原子成立 iff 記録前の成立。
8. trace_executes: 任意slotリストxsと、初期State・合成辺からxsへの既存Traceがあれば、alias/等式のモデル保存転送と実produceIndexの成功を区別したExecutedがある。
9. saturate_executes: 計算閉包には上記Executedがある。追加前提なし。
10. capacity: 計算閉包の長さはtable長以下。
11. stopped: 全slotを候補とする計算閉包のfirstFreshはnone。
12. reachable_checked_step: 任意slot i,jについてiがDerivedなら、出力のcheckedProduceIndex i jはjをstrにextendしたStateを返す。jへの要求辺所属は前提でなく、要求由来の正当化を主張しない。
13. least: 任意述語Pがseed、alias、双方向等式、名前付きIndexの四規則に閉じていれば、計算閉包の全slotでPが成立。
14. output_fixed: 任意slot iについて同じ辺で出力を再飽和した所属 iff 元の閉包への所属。リスト順・原子重複・Stateの構造的一致は主張しない。
15. earlier_equality_pending: table=[10,20,30]、seeds=[0]、links=[(1,0)]、requests=[(20,30)]の旧adapterでproduceIndex 1 2 = none。
16. reverse_equality_reaches: 同じ固定データの新adapterでslot2はDerived。
17. reverse_equality_checked: 同じ固定データの新adapterでcheckedProduceIndex 1 2はslot2をstrにextendしたStateを返す。15〜17は追加前提なし。

## 検証
focused buildを実装担当と統合側で実行。283 jobs PASS。全体build・Audit全体・verify-lean.shはstanding ordersに従って実行していない。新規17定理はAudit.leanに登録。小さな監査ファイルのみtrust=0で実行。標準基盤公理のみ。
```sh
cd lean
ELAN_HOME=../../elan ../../elan/bin/lake build Yulang.CommonRoleDynamicIndexEqualitySource --wfail
# exit 0
```
```text
Build completed successfully (283 jobs).

real	0m0.149s
user	0m0.106s
sys	0m0.061s
```
```sh
ELAN_HOME=../../elan ../../elan/bin/lake env lean --trust=0 /tmp/Cycle47Audit.lean
# exit 0
```
```text
'Yulang.CommonRoleDynamicIndexEqualitySource.edges_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexEqualitySource.derived_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexEqualitySource.saturate_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexEqualitySource.initial_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexEqualitySource.output_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexEqualitySource.output_has_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexEqualitySource.equality_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexEqualitySource.trace_executes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexEqualitySource.saturate_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexEqualitySource.capacity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexEqualitySource.stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexEqualitySource.reachable_checked_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexEqualitySource.least' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexEqualitySource.output_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexEqualitySource.earlier_equality_pending' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexEqualitySource.reverse_equality_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexEqualitySource.reverse_equality_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

real	0m0.930s
user	0m0.718s
sys	0m0.213s
```
`git diff --check`: exit0。禁止された証明抜け道や新公理の導入なし。read-only別レビューで明白な不整合なし。
初回実装の未使用simp警告とleast帰納仮定エラーは修正済み。統合側の最初の計時は/usr/bin/timeが無くexit127、Leanはその試行では起動していない。bash組込timeで再実行し上記成功。

## 未達・範囲
一般B4は未完成。残る橋 source_boundary_adequate、generated_work_closed、saturate_terminates_and_closes、saturated_frontier_exact、resolve_dictionary_order_sound の一般形は今回閉じていない。今回閉じたのは構成された有限str seed/equality断片の一部分のみ。
任意の初期State、非str receiver、parserからのlowering、一般role/where生成、未解決source名の検査は未対応。aliasとIndexが重なる辺はalias転送として実行可能であり、各要求の呼出しを強制しない。全receiverが到達可能とは主張しない。
最新work/dots-auditのX13〜X17とspec06 roles6.3を照合したが、新たなランタイムテストは実行していない。

## 公開と制限
開始心拍はGitHubアプリで公開し読戻し済み。updatedを実時刻より約27秒先の18:00:00Zにした記録ミスがあり、最終心拍は実測UTCで修正する。中断なし。10分未満で実装・検証・公開準備が完了。
成果物8ファイル（新モジュール、root import、Audit登録、README、設計、設計INDEX、報告、心拍）と、integration由来tools/verify-lean.shを保持した全9ファイル差分をwork/dots-mainへ公開予定。公開後にfetchして全tree照合を行い、実際の成否は会話に報告する。integrationその他のbranchへ書き込みなし。
使用量の枠・実行上限の製品上の値は不明。

## 公開後照合
18:07:59Zに9ファイルの公開とfetchを確認。最初のtree照合でtools/verify-lean.shの実行modeが100755から100644になった差を検出したため、内容は変えず100755へ修正して再公開する。全ファイルの内容差はなし。最終読戻し時刻と結果は会話でも報告する。開始から公開後照合まで約10分。
