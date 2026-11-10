# dots cycle 93 — 保持した区間treeの全再帰診断

## 結果と部分目標

**cycle92の実診断treeから取り出す全node列が、独立に生成した有限closure上のbuild列と、順序・重複込みで等しいことを証明した。** その結果、全再帰unsupported診断の列は既存boundaries列と完全に等しく、到達可能な未対応scanを実treeが落とさない。missing childやplan数0のbranchの後も走査する。

新規 `CommonRoleFrontierReachability` は173行、9公開定理。前cycleの「全再帰boundary抽出と独立Reachの対応」という部分目標は閉じた。B4の主定理の主要橋は5本のまま。固定Formの静的treeを一般のstate更新driverや安定後4分類と呼ばない。

## 正確な量化と主張

以下の9定理はすべて `Yulang.CommonRoleFrontierReachability`。

- `candidates_children`（補助）: 任意registry/goalで、実accepted candidatesを順にexpandした全child列は既存children列と等しい。
- `build_nodes`（補助）: 任意Checked registry、slots、Sources、goalで、実buildのpreorder全node列は、独立closureの全goalを同じbuildで構築した列と等しい。順序と多重度を含む。
- `build_goals`（補助）: 同じ任意入力で、実treeの全root goal列は独立closure列と等しい。
- `build_boundaries`（補助）: 同じ任意入力で、実treeから各nodeのoutsideを抽出した全診断列は既存closureから生成したboundaries列と等しい。
- `boundaries_exact`（局所診断の健全性・完全性）: 任意上記入力とtarget/dで、実treeのunsupported診断所属と、独立Reachかつregistry所属かつinspect=noneがiff。
- `failures_exact`（局所診断の健全性・完全性）: 同じ任意入力で、実treeのlocal rigid rejection所属と、独立Reachかつregistry所属かつ独立Rejectsがiff。
- `run_reach_exact`（局所到達の健全性・完全性）: 任意registry/slots/Sources/initial/targetで、実runが返すtreeにtargetがあることと、Checkedかつ独立Reachがiff。
- `run_boundaries_exact`（局所診断の健全性・完全性）: 任意registry/slots/Sources/initial/target/dで、実runが返すtreeにunsupported診断があることと、CheckedかつReachかつregistry所属かつinspect=noneがiff。
- `run_failures_exact`（局所診断の健全性・完全性）: 同様にlocal rejectionの所属と、CheckedかつReachかつregistry所属かつRejectsがiff。

public runは宣言checkerを実際に計算する。callerのChecked、fuel、有限visit列、child成功、model存在、停止証明は前提にない。Reachはtree所属でなく、独立Acceptsと元requirementsからのEdgeで定義される。Typing/inferの全言語健全性・完全性・主型性を新しく証明したわけではない。

## 境界

- endpointsは固定Form。ordinary stateの絞り込み、再materialization、兄弟再訪、K2、最終4分類は扱わない。
- registry/goal/slots/Sourcesは従来と同じcaller入力。Sourcesは同じgoal/declaration/binder tupleをaliasする制限のまま。実source生成、fresh invocation、共有寿命を新しく決めていない。I-13台帳ADに明記した。
- Treeはpublic dataなので、手作りの偽treeにもextractorは動くが、正当性定理は実build/runだけを対象とする。
- failuresは各nodeでのdeclarationの局所拒否であり、role mismatchも含む。goal全体の拒否分類ではない。空registryはrootだけ残し、planなし、unsupportedなし、failuresなし。診断が空であることを成功と同一視しない。
- boundary列には完全なリスト等式の定理がある。failuresには所属iffだけを証明した。その定義が多重度を保持することと、独立なfailure列とのリスト等式を証明したことを混同しない。
- 既存定義、定理、仕様、lakefileは変更していない。新モジュールのimport/Audit/READMEと設計・台帳だけを加えた。

## 検証

最終production Leanに対して次を実行し、すべてexit 0。

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleFrontierReachability --wfail
✔ [309/309] Built Yulang.CommonRoleFrontierReachability (1.1s)
Build completed successfully (309 jobs).
ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang93/boundary-check.lean
exit 0, no diagnostics
ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang93/axioms.lean
'Yulang.CommonRoleFrontierReachability.candidates_children' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierReachability.build_nodes' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierReachability.build_goals' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierReachability.build_boundaries' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierReachability.boundaries_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierReachability.failures_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierReachability.run_reach_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierReachability.run_boundaries_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierReachability.run_failures_exact' depends on axioms: [propext, Quot.sound]
```

回帰は17個の#guardによる実行検査と、2個の一般的なkernel検査付きexample。#guardをkernelで証明した定理とは呼ばない。空registry/zero-child leaf、全child成功、missing first childの後のunsupported/rigid rejection、duplicate親とchildとunsupported宣言、逆順child、前にunsupported宣言があっても後のacceptedを残すこと、深さ4の失敗sibling列、無関係な不正宣言によるglobal checker拒否を検査した。期待値の変更はしていない。

```text
python3 tools/boundary-input-inventory.py --check
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=260; Main=93; Audit=260; ledger mentioned=133. Mention counts are not audit completion counts.
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: . @ 722cadb73 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

`git diff --check`もexit 0。verifyはdiff-onlyで全build/全Audit/AxiomGateのPASSではない。全体のローカル検証は常設指示どおり実行していない。9定理の依存公理は全てpropext/Quot.soundだけ。

初回elaborationではnested Tree recursionのcontext名、dependent matchの分岐、attach/flatMapのリスト等式を修正した。最初のdiff-only gateは未commit LeanファイルのためFAILだった。source commit後に同じgateを再実行してPASS。これらを言語の反例や検証成功として数えていない。

## 公開とreview

source commit: `5a597483b8c1be6d043f3a4117eb9e19f43e350f`。local checkpoint: `722cadb73`。
source tree: `1255f0949f8717bd59e7ddf169801a6ac73364cf`。

8変更pathを個別blobで作り、各返却SHAをlocal hash-objectと照合した。live work/dots-mainのtreeを基にSHA-only treeを作り、全tree SHAがlocal checkpointに一致することを確認した。非force・expected-head更新を使用し、integrationには書かない。ref更新後のtree取得照合とexact-source CIの状態は追記する。報告+最終心拍を含むサイクルの変更は9path。

読み取り専用reviewerは独立Reach、global Checked、固定syntax、Sources alias境界を確認しblockerなし。failuresをgoal分類と呼ばないことと、boundaryリスト等式とfailure所属iffを区別する点を報告に反映した。reviewer自身はbuild/testを実行していない。

## Yulang2との照合

`notes/audit/x-oracle.md`のC3-PARENT-NEGと`y2-claims-role-boundaries-cycle-2.md`のROLE-MORE-003/004を読んだ。旧Y2には宣言whereだけのmissing childを拒否しない差があり、bodyで需要が生じる場合は不足を拒否する。旧挙動を新specへ持ち込まず、spec 6.3とinbox I-5の「子を保持した未完成tree、最終写像は後置」を根拠にした。新しいY2実行はなく、この一般treeを実機で検証したとは言わない。

## 残る主要橋と次の候補

1. `source_boundary_adequate`: parser/declからscope、grouped clause、associated annotation、source occurrence/invocationを実導出する。
2. `generated_work_closed`: state-dependent materialization後の一般childを計算された有限source-template領域へ接続する。
3. `saturate_terminates_and_closes`: 兄弟更新/再生成を安定まで回すPaterson/K2 driver。
4. `saturated_frontier_exact`: 今回の静的treeを実飽和へ接続し、安定後の独立4分類を得る。
5. `resolve_dictionary_order_sound`: 正準source obligation順でのdictionary観察同値。

次の候補は(a) Form区間と実ordinary state materialization carrierの接続、(b) state更新後のtree再計算とsource owner/子結果保持、(c) scope/source生成で未確定なinvocation identityの回答整理。診断用の補助を増やすだけでB4完成へ数えない。

新規意味論判断0件、新規質問0件。既存のinvocation/非線形head等の未回答事項を維持した。

## 復旧・時間・資源

- 開始2026-11-10T18:26:29Z。live integration `6150d77e`、work `10449894`を取得し、standing orders/inboxを再読。ACTIVE、上限なし。前cycle92 completed heartbeat/reportあり。別writer/Lean/Lake/Git processなし。
- 同じworkspace/cacheを継続。integrationを通常mergeした。cycle92 report/heartbeatだけの衝突は、差分を確認し、後から得たexact-source CI成功の追記を保持して解消した（local `ed0e24127`）。integrationのproduction Leanとの差はない。
- startup heartbeat `51bbf7f5`。source公開と最終心拍は上記証跡を追記する。新規cloneなし、空き48G/63G（使用13G）。使用量の枠は不明。
- ログは `../cache/yulang93`。下に回帰script全文を保存。期限2026-11-10T18:52:19Z。
- 報告準備: 2026-11-10T18:36:58Z、経過10.5分。時間を埋めるための定理を追加していない。

## 再実行用回帰script全文

```lean
import Yulang.CommonRoleFrontierReachability
open Yulang
open CommonRoleCaptureNormalization (Form)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleGuardedIntervalPlans (Sources)
open CommonRoleGuardedIntervalFrontier (Tree root branches plans run)
open CommonRoleFrontierReachability
namespace Cycle93BoundaryCheck
set_option maxRecDepth 8192
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 4000000

def mk (role : Nat) (form : Form) : Goal := ⟨role,[(form,form)]⟩
def parent : Declaration := ⟨0,0,[.tick (.var 0)],[(1,[.var 0]),(2,[.var 0])]⟩
def left : Declaration := ⟨1,1,[.var 0],[]⟩
def right : Declaration := ⟨2,2,[.var 0],[]⟩
def rigidRight : Declaration := ⟨2,3,[.tick (.var 0)],[]⟩
def sources : Sources := fun _ _ binder => binder
def goal := mk 0 (.tick .int)
def unknownGoal := mk 0 (.tick (.var 7))
def summary (tree : Tree Nat) :=
  ((goals tree).map (·.role),
   (boundaries tree).map (fun entry => (entry.1.role,entry.2.key)),
   (failures tree).map (fun entry => (entry.1.role,entry.2.key)),
   (plans tree).length)
def inspect (ds : List Declaration) (g : Goal) := (run ds id sources g).map summary

-- Empty diagnostics do not establish a successful plan.
#guard inspect [] goal = some ([0],[],[],0)
#guard (run [] (id : Nat → Nat) sources goal).map goals = some [goal]
#guard inspect [left] (mk 1 .int) = some ([1],[],[],1)
#guard inspect [parent,left,right] goal =
  some ([0,1,2],[],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)],1)
-- The missing first child does not hide the later unsupported child.
#guard inspect [parent,rigidRight] unknownGoal =
  some ([0,1,2],[(2,3)],[(0,3),(1,0),(1,3),(2,0)],0)
#guard (run [parent,rigidRight] (id : Nat → Nat) sources unknownGoal).map goals =
  some [unknownGoal,mk 1 (.var 7),mk 2 (.var 7)]
-- Supported local rejection is separate from unsupported scanning.
#guard inspect [parent,rigidRight] goal =
  some ([0,1,2],[],[(0,3),(1,0),(1,3),(2,0),(2,3)],0)
#guard inspect [rigidRight] (mk 2 (.var 7)) = some ([2],[(2,3)],[],0)
#guard inspect [rigidRight] (mk 2 .int) = some ([2],[],[(2,3)],0)
-- Duplicate accepted parents duplicate entire descendant occurrences.
#guard inspect [parent,parent,rigidRight] unknownGoal =
  some ([0,1,2,1,2],[(2,3),(2,3)],
    [(0,3),(1,0),(1,0),(1,3),(2,0),(2,0),(1,0),(1,0),(1,3),(2,0),(2,0)],0)
-- Duplicate requirements and reversed order remain observable as list order.
def repeated : Declaration := ⟨0,4,[.tick (.var 0)],[(1,[.var 0]),(2,[.var 0]),(2,[.var 0])]⟩
#guard (run [repeated,rigidRight] (id : Nat → Nat) sources unknownGoal).map
  (fun tree => ((goals tree).map (·.role),(boundaries tree).map (fun e => (e.1.role,e.2.key)))) =
  some ([0,1,2,2],[(2,3),(2,3)])
def reversed : Declaration := ⟨0,5,[.tick (.var 0)],[(2,[.var 0]),(1,[.var 0])]⟩
#guard (run [reversed,rigidRight] (id : Nat → Nat) sources unknownGoal).map
  (fun tree => ((goals tree).map (·.role),(boundaries tree).map (fun e => (e.1.role,e.2.key)))) =
  some ([0,2,1],[(2,3)])
-- An unsupported earlier declaration cannot suppress a later accepted one.
def rigidParent : Declaration := ⟨0,6,[.tick (.tick (.var 0))],[]⟩
#guard (run [rigidParent,parent,rigidRight] (id : Nat → Nat) sources unknownGoal).map
  (fun tree => ((goals tree).map (·.role),(boundaries tree).map (fun e => (e.1.role,e.2.key)))) =
  some ([0,1,2],[(0,6),(2,3)])
#guard (run [parent,rigidRight,rigidRight] (id : Nat → Nat) sources unknownGoal).map
  (fun tree => (boundaries tree).map (fun e => (e.1.role,e.2.key))) = some [(2,3),(2,3)]
-- Rejections and scans behind deeper failed siblings are still traversed.
def recursive : Declaration := ⟨0,7,[.tick (.var 0)],[(1,[.var 0]),(0,[.var 0])]⟩
def tower : Nat → Form | 0 => .var 7 | n+1 => .tick (tower n)
#guard (run [recursive] (id : Nat → Nat) sources (mk 0 (tower 4))).map
  (fun tree => ((goals tree).map (·.role),(boundaries tree).map (fun e => (e.1.role,e.2.key)),(plans tree).length)) =
  some ([0,1,0,1,0,1,0,1,0],[(0,7)],0)
-- Global checked-registry refusal is not weakened to reachable declarations.
def growing : Declaration := ⟨8,8,[.var 0],[(8,[.tick (.var 0)])]⟩
#guard (run [parent,left,right,growing] (id : Nat → Nat) sources goal).isNone = true
#guard (run [growing] (id : Nat → Nat) sources goal).isNone = true

-- Independent declarative reach and scan evidence enters the real public run.
example (registry : List Declaration) (checked : CommonRoleIntervalWorkClosure.Checked registry)
    (initial target : Goal) (d : Declaration)
    (reachable : CommonRoleIntervalWorkClosure.Reach registry initial target)
    (present : d ∈ registry) (unsupported : CommonRoleIntervalCandidates.inspect d target = none) :
    ∃ tree, run registry (id : Nat → Nat) sources initial = some tree ∧
      (target,d) ∈ boundaries tree :=
  (run_boundaries_exact registry id sources initial target d).mpr
    ⟨checked,reachable,present,unsupported⟩

-- Conversely, a real stored rejection cannot refer to unreachable work.
example (registry : List Declaration) (initial target : Goal) (d : Declaration)
    (tree : Tree Nat) (returned : run registry id sources initial = some tree)
    (member : (target,d) ∈ failures tree) :
    CommonRoleIntervalWorkClosure.Reach registry initial target :=
  ((run_failures_exact registry id sources initial target d).mp ⟨tree,returned,member⟩).2.1
end Cycle93BoundaryCheck
```

## 公開後の照合（2026-11-10T18:37Z）

source commitのrefをlive APIで再読し、意図した5a597483に一致した。
非truncatedの再取得tree（2,337 entries）はlocal tree SHAと完全一致し、
8変更pathのblob SHAもすべて一致した。既存の他pathは保持されている。
10分心拍は18:37:37Zに作成（11.1分）し、source公開後に別commitで送った。

exact-source CIはこの時点でCore CI/Lean inference kernelともin_progress。
- Core: https://github.com/momota1029/yulang/actions/runs/42877062517
- Lean: https://github.com/momota1029/yulang/actions/runs/42877062502

この状態を全CI成功と呼ばない。結果を得られた場合は追記する。

## 最終報告準備（2026-11-10T18:38:47Z）

sourceのCore CIはcompleted/successを確認した。Lean inference kernelはin_progress。
production Leanはsource公開後に変更していない。全CI成功はまだ主張しない。
11.1分心拍commitは`58138fb723729d6a18c79f544fb2b86c7238d9ec`、
そのtreeもlocal心拍checkpointと完全一致した。最終報告とcompleted心拍を公開して照合する。
ここまでの経過12.3分。

## Exact-source CI完了（2026-11-10T18:39:12Z）

source `5a597483b8c1be6d043f3a4117eb9e19f43e350f` のCore CIとLean inference kernelは
両方completed/successを確認した。Lean proof jobのLean action、全宣言Audit、
source/value/regular/semantic-record examplesの各stepもsuccess。
- Core: https://github.com/momota1029/yulang/actions/runs/42877062517
- Lean: https://github.com/momota1029/yulang/actions/runs/42877062502

これはremote CIの結果であり、ローカル全体検証とは区別する。後続の報告/心拍だけの
commitのCIとも区別する。source公開後にproduction Leanの変更はない。
最終公開準備の経過12.7分。
