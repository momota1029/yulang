# dots cycle 97 — 診断 tree の再利用と実 graph の正確な再生成

## 結果と部分目標

**ordinary 状態の列を処理し、materialized Goal が変わった時だけ完全な診断 tree を作り直す実行版を作った。全状態の出力が既存の public run と完全一致すること、再構築数と再構築 tree の全 node 出現数の上限が元 Goal と宣言から計算できることを証明した。**

新規 `CommonRoleFrontierReplay` は255行、12公開定理。初期 tree を一度作り、その後は元 Goal の materialization を比べ、同一なら直前の tree を使う。状態が変わらない区間の後も処理を続け、後着の証拠を落とさない。`runGraphs` は tree を使い回しても、各時点の ordinary atoms と old demands から実 graph を必ず作り直す。

old demands は時点を表す Nat ごとに独立して渡せる。同じ atom 列が再訪されても、old demands が異なれば正しい新 graph が得られる。guard で、同じ atom 状態3回に対して old demands を空・矛盾制約・空と変え、tree 構築は1回のまま graph edge 数が0・1・0となることを確認した。

今回の部分目標は閉じた。I-4 優先3の停止性へ向けた実行可能な部品であり、実 ordinary solver が状態列を作ることや、その列が停止することは証明していない。**T1c全体、外側 resolve_exact、X13〜X16、B4の5橋は未完成。**

## 定理の量化、前提、側

以下は全て `Yulang.CommonRoleFrontierReplay`。全12定理の側は**補助（実行版の出力一致または進捗上限）**。M1の健全性・完全性・主型性の三つ組を完成したとの主張はない。

1. `replayFrom_snapshots`: 任意の checked registry、slots、Sources、元 Goal、初期atoms、cache、有限状態列について、cache が初期状態の正しい build と等しいなら、全後続 snapshot が各状態の直接 build 列と等しい。Chain不要。
2. `replay_snapshots`: 同じ任意入力で、初期snapshotも含む全出力が全状態の直接build列と等しい。cacheの正しさはpublic計算が構成し、callerの前提ではない。
3. `replayFrom_rebuilds`: 任意cacheを含む任意入力で、後続の再構築数がcycle96の実Goal変化数と厳密に等しい。Chain不要。
4. `replay_rebuilds`: 任意入力で、初期構築を含む回数が1 + 実変化数。
5. `nodeCount_le_domain`: 任意checked registry、slots、Sources、元Goal、任意atomsで、実buildのpreorder出現数がcycle95の有限domain長以下。全closureがvariant domainの連結の1ブロックに入ることを使い、単なる集合包含を長さ上限と取り違えない。
6. `replayFrom_visits`: 任意cache、任意有限状態列について、後続の再構築treeのpreorder出現数の和 ≤ 実変化数 × computed domain長。Chain不要。
7. `replay_bounded`: 任意初期atomsと有限状態列がChainなら、再構築数 ≤ 1 + 元Goalの変数出現数、preorder出現数の和 ≤ 同じ数 × computed domain長。
8. `run_exact`: 任意public入力とoutputについて、成功 iff checked registryが存在しoutputが実replayと等しい。public入口がcheckを計算する。
9. `run_graph_snapshots`: 任意成功runと任意の状態依存old demands関数について、全snapshotのsome列が、各状態の既存public graph runのTree射影の列と等しい。Chain・モデル・子成功不要。
10. `run_computed_bound`: 任意成功runとChainについて、public workDomainが実際に返すboundが存在し、snapshot長が1 + 入力状態列長で、再構築数とpreorder出現数がsourceから計算した上限以下。
11. `refreshGraphs_exact`: 任意の時点依存old demands、任意のatoms→Tree関数、任意有限状態列について、対応するtree列を渡したgraph refreshは成功し、各時点にその時点のold demandsを使う直接graph列と等しい。
12. `runGraphs_exact`: 任意成功replayと任意の時点依存old demandsについて、graph adapterも成功し、その全出力のsome列が各時点の既存public materialized runの完全な出力列と等しい。graphの順序・代替数・各制約を含む等式で、Tree射影だけの結果ではない。

## 境界と未達

- Chainは、各隣接atom列のmembership包含と、後状態のモデルの存在。計算はモデルを受け取らない。正確な出力一致は矛盾状態・非単調列でも成立するが、sourceによる上限にはChainが要る。
- 有限状態列はcallerが渡す。実solverが列を生成するadequacy、fairness、全ordinary更新回数、停止時刻は未達。plateauを停止条件にしていない。
- `visits`は再構築されたtreeの完全なpreorder出現数を合計する会計上の尺度。実装内の全操作・全traversal・runtimeを計測した値ではない。全状態のmaterialization、比較、snapshot列、graph更新の費用は列長に依存する。graph内部vertex数にも上限はない。
- treeはoutside、rejects、未完了child、候補・childの順序と重複を全て保持する。graphも毎回再構築し、ordinary atomsとold demandsを捨てない。
- 実装は既存の明示paired-int detector断片。str/bool/unitや一般semantic entailmentを拒否する仕様ではなく、現実装の範囲。元Goal、slots、Sourcesは固定。invocation/source identityの導出・意味保存は既存の未解決境界。
- 内部refresh zipperは列長不一致ならnoneとし、末尾を切り捨てない。public replayは正確なsnapshot長を構成するため、public adapterではこの不一致に到達しない。
- 新しい意味論判断0件、新質問0件。source/invocation-sharingの既存質問を勝手に解決していない。

## 検証

最終production sourceに以下を実行し、全てexit 0。

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleFrontierReplay --wfail
✔ [313/313] Built Yulang.CommonRoleFrontierReplay (1.1s)
Build completed successfully (313 jobs).

ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang97/boundary-check.lean
exit 0, no diagnostics
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang97/axioms.lean
'Yulang.CommonRoleFrontierReplay.replayFrom_snapshots' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierReplay.replay_snapshots' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierReplay.replayFrom_rebuilds' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierReplay.replay_rebuilds' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierReplay.nodeCount_le_domain' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierReplay.replayFrom_visits' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierReplay.replay_bounded' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierReplay.run_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierReplay.run_graph_snapshots' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierReplay.run_computed_bound' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierReplay.refreshGraphs_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFrontierReplay.runGraphs_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

30個の実行guard、4個のkernel example、補助モデル証明を検査した。空stream、長いplateau、遅延証拠、2slotの変化、既知の初期状態、空goal、closed goal、重複宣言・代替、nested pair/join/tick、同名・slot alias、片方向証拠、str/bool/unit、宣言拒否を含む。非単調列では再構築6回、包含があっても矛盾状態では4回という負例も保持した。tree plateauで増えたrow制約と、同じatom列の時点別old demandsの変更がgraphへ反映されることも確認した。

最後の2定理はmapIdxに由来する標準のClassical.choiceを含み、それ以外の10定理はpropext / Quot.soundのみ。新規公理の宣言はない。

```text
python3 tools/boundary-input-inventory.py --check
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=264; Main=93; Audit=264; ledger mentioned=137. Mention counts are not audit completion counts.

bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: . @ 7e8ba0d7c (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

`git diff --check` exit 0。指示どおり全ローカルbuild、全Audit/AxiomGateは未実行。verifyのPASSはdiff-only。

独立read-only reviewerは、計算が実際にcacheを再利用すること、任意状態列の完全なsnapshot等式、ブロックによる重複込み長さ上限、graphを毎回更新することを確認し、blocking issueなし。review中にoldがatom列だけで索引されている制限を指摘されたため、時点ごとのNat索引に一般化し、同一atoms・異なるold demandsのguardを加えた。最終hashを再reviewして問題なし。reviewer自身のbuildと私の検証は区別する。

時点索引へ一般化した最初の証明では局所letのatomsがsimpで一致せずbuildが失敗した。pairのfstを直接使う証明へ直し、production build・全guard・全12定理監査を再実行した。期待値や主張の弱化はない。

## Yulang2との照合

開始時にwork/dots-auditを取得し、x-oracleのX13〜X16と関連結果を読んだ。shared box、深さ2、同頭の局所区間、異頭の近似という既存観測を、任意状態列のreplayや飽和driverの実機証明とは呼ばない。新しいYulang2実機実行なし。spec6.3のordinary制約による絞り込み・遅延判断に従い、unique implを絞り込みの根拠にしていない。

## 復旧、公開、時間

開始は2026-11-10T20:27:36Z、指定期限20:52:19Z。integration/workは開始時ともにd1b6dfbb。standing orders/inboxを再取得しACTIVEと上限なしを確認。前cycle96はcompletedと報告あり、前writer/Lean processもなし。正常再開で、crash recoveryではない。integration/work/auditを明示fetchし、integrationを通常mergeして既存workspace/cacheを再利用した。

source commit: `bb4f5ca0365aa0c039e4dd81403723a08712f4c3`。
source tree: `8b6c75bc4923f7bd9ced723f214a92efbda3a135`。
local source commit: `7e8ba0d7c`、heartbeat込み `342fb5a82`。
source SHA256: `a67a29289dd7cda13b32bb0f618a56cabe2b31d78246728040abf5ef859b1208`。

8source/document pathを個別blobで作成し、全SHAをlocal hash-objectと照合。live work treeをbaseにSHA-only treeを作り、tree全体がlocal write-treeと一致。非force・expected-head更新後にrefと非truncated recursive tree（2349 entries）を取得し、8変更blobを全照合した。他pathは保持。source公開は開始約14.1分、20分の途中公開期限より前。source公開後はproduction Leanを変更しない。

startup heartbeat `178cdd92`、進捗heartbeat `86d0e78f`。報告とcompleted heartbeatを最終公開し、そのref/tree/blobを照合して終了する。今回の変更は報告・heartbeatを含め10path。空き47G、cloneやcacheコピーなし。使用量の枠は不明。ログは `../cache/yulang97`。

## B4に残る5橋と次の候補

1. `source_boundary_adequate`: parser/declからscope、annotation、source occurrence/invocationを導く。
2. `generated_work_closed`: 固定templateと明示int evidenceから一般状態依存生成仕事へ拡張する。
3. `saturate_terminates_and_closes`: 今回の再構築budgetとPaterson closureを実ordinary solverの状態生成・fairness・停止と結び付ける。不変ordinary更新やgraph更新の無制限反復を隠さない。
4. `saturated_frontier_exact`: 実飽和と安定後の独立4分類を接続する。
5. `resolve_dictionary_order_sound`: 正準source obligation順のdictionary観察同値。

次候補: (a) real ordinary state更新がChainを満たす具体的境界、(b) source invocation再訪時の意味保存、(c) bounded rebuildsとordinary workの進捗を結ぶ実scheduler。既存のsource identity質問の回答を仮定の外へ隠して完成とはしない。

## 再実行可能な境界回帰

```lean
import Yulang.CommonRoleFrontierReplay
open Yulang
open CommonRoleCaptureNormalization (Form)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleGuardedIntervalPlans (Sources Plan)
open CommonRoleFrontierReplay
open CommonRoleMaterializationProgress (Chain)
open Core.PresenceGeneration (Comp TyTerm)
open PresenceNormalForm (Atom All)
namespace Cycle97BoundaryCheck
set_option maxRecDepth 8192
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 4000000

def slots : Nat → Fin 2 := fun n => ⟨n % 2, Nat.mod_lt n (by decide)⟩
def sources : Sources := fun _ _ binder => binder
def eqn (i : Fin 2) (base : Inference.Base) := CommonRoleCandidateStateFrontier.equality i base

def parent : Declaration := ⟨0,0,[.tick (.var 0)],[(1,[.var 0]),(2,[.var 0])]⟩
def left : Declaration := ⟨1,1,[.var 0],[]⟩
def right : Declaration := ⟨2,2,[.int],[]⟩
def growing : Declaration := ⟨9,9,[.var 0],[(9,[.tick (.var 0)])]⟩
def goal : Goal := ⟨0,[(.tick (.var 0),.tick (.var 0))]⟩
def scalarGoal : Goal := ⟨0,[(.var 0,.var 1)]⟩
def one := eqn 0 .int
def both := one ++ eqn 1 .int

def counts (registry : List Declaration) (g : Goal) (initial : List (Atom (Fin 2)))
    (states : List (List (Atom (Fin 2)))) :=
  (run registry slots sources g initial states).map fun r => (r.snapshots.length,r.rebuilds,r.visits)
def boundaries (states : List (List (Atom (Fin 2)))) :=
  (run [parent,left,right] slots sources goal [] states).map fun r => r.snapshots.map fun tree =>
    (CommonRoleFrontierReachability.boundaries tree).map (fun pair => (pair.1.role,pair.2.key))

#guard counts [parent,left,right] goal [] [] = some (1,1,3)
#guard counts [parent,left,right] goal [] [[],[],[],[]] = some (5,1,3)
#guard counts [parent,left,right] goal [] [[],[],one,one,one] = some (6,2,6)
#guard boundaries [[],[],one,one,one] = some [[(2,2)],[(2,2)],[(2,2)],[],[],[]]
#guard counts [parent,parent,left,right] goal [] [[],one,one] = some (4,2,10)
#guard counts [parent,left,left,right,right] goal [] [one] = some (2,2,6)
#guard counts [parent,left,right] goal one [one,both,both] = some (4,1,3)
#guard counts [] scalarGoal [] [[],one,one,both,both] = some (6,3,3)
#guard counts [] scalarGoal both [both,both,both] = some (4,1,1)
#guard counts [] ⟨0,[]⟩ [] [one,[],both] = some (4,1,1)
#guard counts [] ⟨0,[(.tick .int,.join .int .int)]⟩ [] [one,[],both] = some (4,1,1)
#guard counts [parent,left,right] goal [] [eqn 1 .int] = some (2,1,3)
#guard counts [parent,left,right] goal [] [[.tyLe (.var 0) (.base .int)]] = some (2,1,3)
#guard counts [parent,left,right] goal [] [eqn 0 .str,eqn 0 .bool,eqn 0 .unit] = some (4,1,3)
#guard counts [parent,left,right,growing] goal [] [one] = none
-- Nonmonotone streams remain exact but do not satisfy the source rebuild bound.
#guard counts [parent,left,right] goal [] [one,[],one,[],one] = some (6,6,18)
-- Inclusion alone is insufficient: inconsistent first evidence can undo int.
#guard counts [parent,left,right] goal [] [one,eqn 0 .str ++ one,one ++ eqn 0 .str] = some (4,4,12)
-- Source aliasing is preserved, while counts need not be the sharpest possible.
#guard counts [] ⟨0,[(.pair (.var 0) (.tick (.join (.var 2) (.var 1))),.var 0)]⟩ []
  [one,both,both] = some (4,3,3)
#guard counts [parent,left,right] goal one [one ++ one,one ++ one ++ one] = some (3,1,3)
-- New row constraints are not lost: they must go to a fresh ordinary graph.
#guard counts [parent,left,right] goal one [one ++ [.rowLe (.var 0) (.var 1)]] = some (2,1,3)
#guard (CommonRoleStateMaterializedFrontier.run [parent,left,right] slots sources
  (one ++ [.rowLe (.var 0) (.var 1)]) [] goal).map
  (fun out => out.2.map (fun graph => graph.rows.length)) = some [1]
#guard (CommonRoleStateMaterializedFrontier.run [parent,left,right] slots sources one [] goal).map
  (fun out => out.2.map (fun graph => graph.rows.length)) = some [0]

def assignment : Fin 2 → Comp Common.model := fun _ => (.base .int,fun _ => False)
theorem eqn_models (i : Fin 2) : All Common.model assignment (eqn i .int) := by
  simp [All, eqn, CommonRoleCandidateStateFrontier.equality, Atom.Holds,
    TyTerm.eval, assignment, Common.model, Common.subtype_refl]
theorem one_models : All Common.model assignment one := eqn_models 0
theorem both_models : All Common.model assignment both :=
  (PresenceNormalForm.all_append ..).mpr ⟨one_models,eqn_models 1⟩
theorem positive_chain : Chain ([] : List (Atom (Fin 2))) [[],one,one,both,both] := by
  refine ⟨⟨?_,assignment,PresenceNormalForm.all_nil Common.model assignment⟩,⟨⟨?_,assignment,one_models⟩,
    ⟨⟨?_,assignment,one_models⟩,⟨⟨?_,assignment,both_models⟩,⟨⟨?_,assignment,both_models⟩, trivial⟩⟩⟩⟩⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; exact h
  · intro atom h; exact List.mem_append_left _ h
  · intro _ h; exact h

theorem checked : CommonRoleIntervalWorkClosure.Checked [parent,left,right] := by decide +kernel

example : (replay [parent,left,right] checked slots sources goal [] [[],one,one,both,both]).rebuilds ≤
    1 + CommonRoleMaterializationProgress.potential goal ∧
    (replay [parent,left,right] checked slots sources goal [] [[],one,one,both,both]).visits ≤
      (1 + CommonRoleMaterializationProgress.potential goal) *
        (CommonRoleStateMaterializedFrontier.domain [parent,left,right] checked goal).length :=
  replay_bounded _ _ _ _ _ _ _ positive_chain

example (registry : List Declaration) (g : Goal) (initial : List (Atom (Fin 2)))
    (states : List (List (Atom (Fin 2)))) (output : Replay 2)
    (returned : run registry slots sources g initial states = some output)
    (old : List (Atom (Fin 2)) → Plan (Fin 2)) :
    output.snapshots.map some = (initial :: states).map (fun atoms =>
      (CommonRoleStateMaterializedFrontier.run registry slots sources atoms (old atoms) g).map Prod.fst) :=
  run_graph_snapshots _ _ _ _ _ _ _ returned old

example (registry : List Declaration) (g : Goal) (initial : List (Atom (Fin 2)))
    (states : List (List (Atom (Fin 2)))) (output : Replay 2)
    (returned : run registry slots sources g initial states = some output) (chain : Chain initial states) :
    ∃ bound, CommonRoleStateMaterializedFrontier.workDomain registry g = some bound ∧
      output.snapshots.length = 1 + states.length ∧
      output.rebuilds ≤ 1 + CommonRoleMaterializationProgress.potential g ∧
      output.visits ≤ (1 + CommonRoleMaterializationProgress.potential g) * bound.length :=
  run_computed_bound _ _ _ _ _ _ _ returned chain

-- Full graph replay reuses diagnostics but always refreshes ordinary constraints.
#guard (runGraphs [parent,left,right] slots sources goal one
  [one ++ [.rowLe (.var 0) (.var 1)]] (fun _ => [])).map
  (fun out => (out.1.rebuilds,out.2.map (fun pair => pair.2.map (fun graph => graph.rows.length)))) =
    some (1,[[0],[1]])
#guard (runGraphs [parent,left,right] slots sources goal [] [[],one,one] (fun _ => [])).map
  (fun out => out.2.map (fun pair => pair.2.length)) = some [0,0,1,1]
#guard (runGraphs [parent,parent,left,right] slots sources goal one [one] (fun _ => [])).map
  (fun out => out.2.map (fun pair => pair.2.length)) = some [2,2]
#guard (runGraphs [parent,left,right,growing] slots sources goal [] [] (fun _ => [])).isNone
#guard (refreshGraphs (n := 2) (fun _ => []) [] []).isSome
#guard (refreshGraphs (n := 2) (fun _ => []) [[]] []).isNone
#guard (refreshGraphs (n := 2) (fun _ => []) []
  [CommonRoleGuardedIntervalFrontier.build [parent,left,right] checked slots sources goal]).isNone

example (registry : List Declaration) (g : Goal) (initial : List (Atom (Fin 2)))
    (states : List (List (Atom (Fin 2)))) (output : Replay 2)
    (returned : run registry slots sources g initial states = some output)
    (old : Nat → Plan (Fin 2)) :
    ∃ graphs, runGraphs registry slots sources g initial states old = some (output,graphs) ∧
      graphs.map some = (initial :: states).mapIdx (fun i atoms =>
        CommonRoleStateMaterializedFrontier.run registry slots sources atoms (old i) g) :=
  runGraphs_exact _ _ _ _ _ _ _ _ returned


-- Identical atom states can carry independently different old demands.
def emptyDecl : Declaration := ⟨1,1,[],[]⟩
def changingOld (i : Nat) : Plan (Fin 2) :=
  if i = 1 then [(99,(.base .int,.base .str))] else []
#guard (runGraphs [emptyDecl] slots sources ⟨1,[]⟩ [] [[],[]] changingOld).map
  (fun out => (out.1.rebuilds,out.2.map (fun pair => pair.2.map (fun graph => graph.edges.length)))) =
    some (1,[[0],[1],[0]])
end Cycle97BoundaryCheck
```

報告準備時刻: 2026-11-10T20:43:20.579331+00:00、経過 15.7分。Exact-source CIは別途確認し、未確認をPASSとしない。

## Exact-source CI と最終公開準備

source `bb4f5ca0365aa0c039e4dd81403723a08712f4c3` のCore CIとLean inference
kernelは両方completed/success。Lean proof jobの全build、全宣言Audit、
source/value/regular/semantic record examplesの各stepもsuccessを確認した。
ローカル全体検証とは区別する。production Leanの後続変更なし。

- Core: https://github.com/momota1029/yulang/actions/runs/42897820323
- Lean: https://github.com/momota1029/yulang/actions/runs/42897820478

最終公開準備: 2026-11-10T20:44:05Z。報告とcompleted heartbeatを非force公開し、最終ref/tree/blobを照合する。
