# dots cycle 19 — finite autonomous associated feedback

開始 2026-11-08T23:30:04Z。integration `0b0d30294`、I-7〜I-10、上限24を確認。cycle18のcompleted心拍と報告、復旧終了を確認後に開始し、並行writerなし。最新integrationをmerge（`23e30db6b`）。今回25分以内を優先。

## 達成と境界

2新モジュール、12監査登録定理。外部state traceを入力しない有限feedback driverを作った。各段階で収集済み更新IDからordinary stateを再構成し、実producerによるsource Reachを再計算し、新規更新IDを一つ追加する。有限ID数kで停止し、最終Reachから発生する更新IDがすべて収集済みになる。

第二層ではordinary stateの再構成を、既存の実関連型宣言から等式を計算するAssociatedBatch.runに具体化した。最終モデルは初期ordinary制約と収集した宣言由来等式の連言に厳密に一致する。最終Reachの発生する全等式を同じ最終assignmentが満たす。

**未達**: 有限request table、固定receiver、source-nodeから更新IDへのemit対応は入力のまま。一般source loweringから導いたとは主張しない。一般区間、更新でreceiver自体が変わるassociated request、最小解、順序独立、一般B4の健全性/完全性/主型性、X13〜16外側PROVEDは未達。過去にReachだったnodeの更新は保持するため、最終Reachのみの最小モデル集合とは主張しない。実装断片の制限であり仕様が拒否する範囲ではない。

## 定理（全て任意の型パラメータn,kと該当データを量化）

`CommonRoleFiniteFeedback`:
- `loop_nodup`（補助）: 任意のrules関数/fuel/初期seenでseenが重複なしなら実行結果も重複なし。
- `loop_closed`（補助）: 任意のrules/fuel/seen、seen重複なし、k≤seen.length+fuelを前提に、任意のfactが最終rulesでEnabledなら最終結果に含まれる。rulesの単調性は仮定しない。
- `feedback_enabled`（補助）: 任意registry/root/decode/emit/seen/factについてEnabled iff 現状態でReachなnode qが存在しfact∈emit q。
- `collect_nodup`（補助）: 任意registry/root/decode/emitの収集結果は重複なし。
- `collect_capacity`（停止の補助）: 同じ全データについて収集結果長≤k。
- `collect_closed`（閉包の補助）: 任意registry/root/decode/emit/q/factで、qが最終状態のReachかつfact∈emit qならfactは収集結果に属する。
- `visits_exact`（Reachの健全性・完全性）: 任意registry/root/decode/emit/qについて最終visits所属 iff 最終状態の独立Reach。

`CommonRoleAssociatedFeedback`（さらに任意の関連型env/roles、env.coresのWellFormed証拠wfを量化）:
- `decode_models`（ordinaryモデルの健全性・完全性）: 任意seed/table/seen/assignmentで、再構成ordinary atomsが満たされる iff 初期atomsが満たされ、seenの全ID iと全headについてComputed(table i,head)ならassignmentの出力slotがheadとEquivalent。
- `collected_bounded`（停止の補助）: 任意registry/root/seed/table/emitで収集結果は重複なし、長さ≤k。
- `final_models`（ordinaryモデルの健全性・完全性）: 任意registry/root/seed/table/emit/assignmentについて最終ordinary atomsの充足 iff 初期atomsの充足かつ収集済み全i/全headのComputed等式の充足。
- `reachable_equation`（健全性の補助）: 任意registry/root/seed/table/emit/assignment/q/i/headで、assignmentが最終atomsのモデル、qが最終Reach、i∈emit q、Computed(table i,head)を前提に、そのassignmentのtable iの出力slotはheadとEquivalent。
- `final_visits_exact`（Reachの健全性・完全性）: 任意registry/root/seed/table/emit/qについて最終visits所属 iff 実宣言由来等式を反映した最終stateの独立Reach。

新しい主型性定理なし。一般B4の5橋はまだ5本とも一般形が残る。bridge2で外部traceという前提を除き、実宣言由来のordinary等式を接続したが、有限更新adapterの導出は未達。
次は (1) source closureからrequest table/emitの導出とprovenance、(2) 変動receiverのassociated値と安定時の順序独立、(3) 独立な診断treeと辞書正準順。

## 検証

`git fetch origin integration/m1-final:refs/remotes/origin/integration/m1-final work/dots-main:refs/remotes/origin/work/dots-main` 成功。
`git merge --no-edit origin/integration/m1-final` 成功。
`git fetch origin work/dots-audit:refs/remotes/origin/work/dots-audit` 成功。
`ELAN_HOME=/workspace/scratch/1d0b4aaa3394/dots-probe-elan`、そのbinをPATHに設定。

`cd lean && lake build --wfail Yulang.CommonRoleFiniteFeedback` exit0、全文:
```
✔ [287/287] Built Yulang.CommonRoleFiniteFeedback (1.0s)
Build completed successfully (287 jobs).

real 0m1.146s
user 0m0.863s
sys 0m0.397s
```
`cd lean && lake build --wfail Yulang.CommonRoleAssociatedFeedback` exit0、最終出力全文:
```
✔ [289/289] Built Yulang.CommonRoleAssociatedFeedback (1.0s)
Build completed successfully (289 jobs).

real 0m1.149s
user 0m0.800s
sys 0m0.422s
```
途中の初回ビルドのみ失敗: head型をRoles.Termと書いたがComputedのheadはInference.Base。型注釈を修正後に成功。検証未完コードは公開していない。
`lake env lean /tmp/cycle19-audit.lean` exit0。12定理すべてpropext/Classical.choice/Quot.soundの部分集合のみ。sorry/new axiom/native_decide不使用。`git diff --check`成功。
standing ordersに従い全体lake build、全Audit、verify-lean.shは実行していない。全体PASSは主張しない。

## Yulang2との照合

最新監査枝x-oracle X13〜16を読んだ。内部更新の順序や到達可能性はCLIから直接観測されず未照合。check0は今回の証明の根拠ではない。spec6.3の安定まで最終化を遅延する方針に対する内部補助driver。新しい意味論を決めず、質問ノート追加なし。

## 公開と資源

ローカルcommit `ca66207c0`、`bc5ca8735`。成果6ファイルをcontents APIで一つずつ公開。Yulang/Audit/READMEはremote blobがローカル基点と一致することを確かめて、APIメモリ内で末尾追記。巨大ファイルの本文を会話に展開しなかった。成果6パスの公開後tree照合は一致、報告・completed心拍を加え計8パス。

空き容量は開始19GB。既存未公開commitを持つcloneは消さず、cache複製なし。使用量枠への計上は不明。中断・承認待ち・環境再作成なし。最終公開hashと終了時刻はcompleted心拍および会話の結果に記録する。

成果照合終了: 2026-11-08T23:36:20Z。開始から約6分。終了時空き19GB。
