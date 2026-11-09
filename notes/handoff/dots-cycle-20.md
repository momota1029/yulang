# Yulang Lean cycle 20

開始 UTC 2026-11-08T23:57:30Z。成果検証・公開照合 2026-11-09T00:03:14Z（約6分）。
基点 integration/m1-final `46633e30c`。前回19のcompleted心拍と報告を確認、並行writerなし。
最新standing/inbox I-4〜I-10を再読、ACTIVE、最大24。25分上限とfocused-onlyを優先。

## 成果と未達

computed source closure各Nodeのassociated Request注釈から、有限tableとemitを計算した。
従来入力だった独立のk/table/emitを、一つの有限source注釈にまとめ、所属のiffと最終Reachの
関連型等式を証明した。別に、非単調なfeedbackの独立Traceを定義し、全実行がTraceを持ち、
収集済みの全更新には過去の実Reach nodeという由来があることを証明した。

**注釈そのものは入力であり、parserや一般source宣言からのloweringは未証明**。
receiver固定、int-only/unary/capture-bearing source断片、first-hit productionの制限を維持。
過去のReachから収集した等式は残る。最終Reach-only最小解、兄弟順序独立、一般区間、
一般B4の健全性/完全性/主型性、X13〜16の外側PROVEDは未達。
仕様の拒否規則でなく実装断片の制限。意味論の新しい選択はしていない。

## 定理の日本語主張

全て任意のslot数n、registry、rootを量化。Adapterはさらに任意の各Nodeへの有限Request注釈を量化。
- `CommonRoleSourceAssociatedAdapter.entries_exact`（健全性/完全性の補助）:
  任意q,rで、計算entriesに(q,r)が含まれる iff rはqの注釈に含まれる。
- `emitted_sound`（健全性の補助）: 任意qと計算entriesの添字iでi∈emit qならtable i∈annotations q。
- `emitted_complete`（完全性の補助）: 任意q,rでr∈annotations qなら、i∈emit qかつtable i=rのiが存在する。
- `adapter_exact`（両方向の補助）: 上記二方向のiff。
- `reachable_equation`（健全性の補助）: 任意env/rolesとenv.coresのWellFormed証拠wf、seed、
  assignment、最終ordinary atomsを満たす証拠、最終Reach q、r∈annotations q、headとComputed r head
  を前提に、assignment r.outputの型はbase headとEquivalent。
- `bounded`（停止の補助）: 同じenv/roles/wf/seedについて収集ID数は計算entries長以下。
- `collected_source_origin`（健全性の補助）: 同じenv/roles/wf/seedと収集済みiについて、
  初期空集合からの合法Traceで到達するseenと、そのdecode seenでReachなqが存在し、table i∈annotations q。

Traceの定理はさらに任意の有限ID数k、decode関数、emit関数を量化。単調性は仮定しない。
- `CommonRoleFeedbackTrace.trace_trans`（補助）: 任意a,b,cとTrace a b、Trace b cからTrace a c。
- `loop_trace`（健全性の補助）: 任意fuelと初期seenに対して、実loop結果へのTraceが存在する。
- `trace_origin`（健全性の補助）: 任意start,finish、Trace start finish、fact∈finish、fact∉startから、
  Trace start seenかつdecode seenでReach qかつfact∈emit qであるseen,qが存在する。
- `collected_origin`（健全性の補助）: 任意の収集済みfactについて、上のstart=[]の由来が存在する。

新しい主型性定理なし。B4の一般形は**5橋とも残る**。今回はbridge1/2のadapterと更新由来を接続。
次の1〜3補題: (1) 実sourceからannotationの導出と受け取りslotのprovenance、
(2) 変動receiverと順序独立の飽和、(3) 独立診断treeと正準辞書の分類。

## 検証

`git fetch origin integration/m1-final:refs/remotes/origin/integration/m1-final`、
`git fetch origin work/dots-main:refs/remotes/origin/work/dots-main`、
`git merge --no-edit origin/integration/m1-final` 成功。
`git fetch origin work/dots-audit:refs/remotes/origin/work/dots-audit` 成功。
ELAN_HOMEは既存dots-probe-elan、Lean4 v4.35.0を再使用。

`cd lean && lake build --wfail Yulang.CommonRoleSourceAssociatedAdapter Yulang.CommonRoleFeedbackTrace`
終了コード0、最終出力全文:
```
✔ [291/291] Built Yulang.CommonRoleSourceAssociatedAdapter (1.0s)
Build completed successfully (291 jobs).

real	0m1.250s
user	0m0.861s
sys	0m0.427s
```
`lake env lean /tmp/cycle20-audit.lean` 終了コード0、全文:
```
'Yulang.CommonRoleSourceAssociatedAdapter.entries_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceAssociatedAdapter.emitted_sound' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceAssociatedAdapter.emitted_complete' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceAssociatedAdapter.adapter_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceAssociatedAdapter.reachable_equation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceAssociatedAdapter.bounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceAssociatedAdapter.collected_source_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleFeedbackTrace.trace_trans' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFeedbackTrace.loop_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFeedbackTrace.trace_origin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFeedbackTrace.collected_origin' depends on axioms: [propext, Classical.choice, Quot.sound]
```
初回はList.get/getElemの簡約、Subtype等値のBEq、inductiveの明示引数のエラーで失敗。
修正後にfocusedビルドと11定理の公理監査が成功。sorry/新公理/native_decide不使用。
`git diff --check`成功。**全体lake build、全Audit、verify-lean.shは指示どおり未実行**。
verify-lean.shの出力・終了コードは存在しない。全体PASSとは報告しない。

## Yulang2との照合

監査枝x-oracleのX13周辺を読んだ。内部のsource注釈・TraceはCLIで直接照合していない。
既存のassociated declaration計算とspec6.3の安定まで遅延する方針に接続した補助定理。
旧実機のcheck成功を今回の意味保存の根拠にしていない。質問ノート追加なし。

## 公開・資源・制限

ローカルcommit a8615839f、252c2eec9、93dba89e0。
開始心拍8dd7480f8。最新integrationの既存blobだけを取り込む2親merge47903f6f0をwork/dots-mainへ公開。
spec/planの本文を編集していない。自作成果6pathsはcontents APIで一つずつ公開。
Yulang/Audit/READMEはremote基点blob一致を確認しAPIメモリ内で末尾追記。巨大本文を会話へ展開せず。
成果6pathsのremote/local diff空を確認（086ce565a）。報告とcompleted心拍を加えて自作公開8paths。
前回成果を消さず、他branchへ書き込まず。公開後最終hash/8paths照合は会話の完了報告へ。

空き容量開始19GB、終了19GB。cacheコピーなし。中断・環境再作成・承認待ちなし。
使用量枠への計上は不明。全所要時間は完了心拍で確定、現時点約6分。
