# dots cycle 46: finite string Index input consistency
開始 UTC 2026-11-09T17:27:42Z。基点 integration/m1-final a96f61b6ae3e903055833017418c15861d4081b5。
前回 cycle45 の completed 心拍と報告を確認。並行書き込みなし。統合時の報告・心拍の競合は統合版を採用した後、既公開の cycle45 最終読戻し記録を保持した。STOP なし。サイクル数上限なし。今回25分以内。

## 部分目標と結果
明示的 str seed と slot 型等式だけから構成される実初期 State について、具体的モデルを構成して最終整合性を証明し、実 producer 実行の外部最終モデル前提を除く部分目標は閉じた。任意の不透明な初期制約を扱う一般化ではない。
設計を notes/design/2026-11-09-cycle46-index-consistency.md に先に記録した。意味論の新しい判断はなく、新質問ノートなし。

## 定義と全定理
新モジュール Yulang.CommonRoleDynamicIndexConsistentSource。以下の名前はこの名前空間内。
定義 stringAssignment は全slotの型がstr、effectが空の割当。addEqualities は型等式を実 State の原子・grammar に追加。input は空 State に指定str seedと型等式を追加する。

1. addEqualities_models: 任意の自然数n、State s、Fin nの対の有限リストlinks、割当aについて、追加後の全原子が成立することと、sの全原子が成立し、linksに属する全対(i,j)でa iの型とa jの型が同値であることは同値。effectの等式は要求しない。
2. input_models: 任意のn、seedリスト、links、割当aについて、inputの全原子が成立することと、全seed iでa iの型がstrと同値であり、全link(i,j)で型が同値であることは同値。
3. input_has_model: 任意のn、seedリストとlinksについて、stringAssignmentはinputの全原子を満たす。追加前提なし。
4. output_has_model: 任意の有限source table、そのslotのseedとlinks、および有限名前付きrequestsについて、stringAssignmentはinputから計算したoutputの全原子を満たす。scope、非循環性、重複なしの前提はない。
5. output_consistent: 同じ任意のtable/seeds/links/requestsについて、計算outputのconsistentはtrue。追加前提なし。
6. saturate_executes: 同じ任意のtable/seeds/links/requestsについて、source同一性を追加した実inputからのsaturate結果には実producerのExecuted証跡がある。外部の最終モデル存在前提はない。未到達要求の成功は主張しない。
7. checked_success_iff: 同じ任意のtable/seeds/links/requestsについて、checked runが.ok outとなるモデル付きoutが存在することと、全requestsがWellScopedであることは同値。scope判定の成功と全要求の解決は異なる。
8. reachable_checked_step: 同じ任意のtable/seeds/links/requestsとslot i,jについて、source同一性追加後inputからrequestsに沿ってiがDerivedであることを前提に、計算outputで実checkedProduceIndex i jはjをstrにextendしたStateを返す。jについて要求辺の所属を仮定しない。
9. shared_chain_reachable: table=[10,10,20,30]、seed=[0]、links=[(0,1)]、requests=[(10,20),(20,30)]の固定例でslot3はDerived。追加前提なし。
10. shared_chain_checked: 同じ固定例の計算outputについて実checkedProduceIndex 2 3はslot3をstrにextendしたStateを返す。追加前提なし。
11. unseeded_still_pending: table=[10,20]、空seed/links、requests=[(10,20)]の固定例で計算outputのproduceIndex 0 1はnone。整合性とscopeだけでreceiver証拠は生まれない。

## 検証
以下を実行。helperの初回コンパイルは1.1秒、282 jobs PASS。統合側で再実行しexit0、計測1秒未満（秒単位0秒）。
```sh
cd lean
ELAN_HOME=../../elan ../../elan/bin/lake build Yulang.CommonRoleDynamicIndexConsistentSource --wfail
```
```text
Build completed successfully (282 jobs).

```
新規11定理をAudit.leanに登録。小さな監査ファイルでのみ検査:
```sh
ELAN_HOME=../../elan ../../elan/bin/lake env lean --trust=0 /tmp/Cycle46Audit.lean
```
終了コード0。出力全文:
```text
'Yulang.CommonRoleDynamicIndexConsistentSource.addEqualities_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexConsistentSource.input_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexConsistentSource.input_has_model' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexConsistentSource.output_has_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexConsistentSource.output_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexConsistentSource.saturate_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexConsistentSource.checked_success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexConsistentSource.reachable_checked_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexConsistentSource.shared_chain_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexConsistentSource.shared_chain_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexConsistentSource.unseeded_still_pending' depends on axioms: [propext, Quot.sound]

```
標準のpropext/Classical.choice/Quot.soundのみ。全体build、全Audit、verify-lean.shはstanding orders最新追記に従い未実行。従って全体PASSは未確認。
work/dots-auditをfetchしnotes/audit/x-oracle.mdのX13–X17を確認。最初に誤ったnotes/handoff/x-oracle.mdを探したが正しいパスで読めた。実機oracleは限定された例であり一般B4の証明ではない。今回新しい実機テストは行っていない。

## 未達と次の一手
B4全体の残りは引き続き5橋: source_boundary_adequate, generated_work_closed, saturate_terminates_and_closes, saturated_frontier_exact, resolve_dictionary_order_sound。
今回閉じたのは有限str入力断片のモデル存在と実実行。任意初期Stateの整合性、追加slot等式に沿う完全な証拠伝播、異種role/区間/where子の一般化は未達。
次候補: (1) 初期slot等式を実evidence経路へ接続する局所閉包、(2) 対象source構文からこのinputへの境界、(3) 未到達receiverを保持する診断への接続。一般B4完成、X全件解決とはしない。

## 公開・運用
対象はwork/dots-mainのみ。新Lean、root import、Audit登録、README、設計、今回報告、心拍の7ファイルを今回成果として公開する。統合差分も保持し、期待head付き非forceで更新後、fetchして全treeを照合する。
開始心拍を公開し読戻し済み。開始時elapsed_min=2は実時間約59秒の丸め誤記であり、最終値は実時計から再計算する。
中断・クラッシュなし。開始空き48GB、ビルドキャッシュ再利用、別clone/キャッシュコピーなし。使用量の枠と消費量は取得できず不明。

検証終了・公開準備 UTC 2026-11-09T17:34:28Z、ここまで6.78分。終了空き48GB。公開後の照合結果と最終所要時間は会話報告に記す。


### 公開後の照合記録
成果公開commit 06d624b49d789b53057bc4400365a07ce7bf805b、7ファイル。expected head ec833fdc8 に対する非force更新成功。
fetch後の全tree比較exit0、integration先頭が祖先である検査exit0、completed心拍をGitHubアプリで読戻した。ローカル作業木clean。
検証済みtree d07f14e1a4a7a934611f3a2968119f7b9f28a031。
照合終了 UTC 2026-11-09T17:37:03Z、開始から9.37分。この段落と最終心拍時刻のみを追加公開する。
