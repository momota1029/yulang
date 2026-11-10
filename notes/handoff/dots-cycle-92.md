# dots cycle 92 — 未完成の子を残す区間診断tree

## 結果と部分目標

**固定Form区間に対し、acceptedな親候補と全where子を残す有限診断treeを実際に構築し、そのcomplete-planへの消去がcycle91の計算結果とリスト全体で等しいことを証明した。** 子のplanが0個でも親候補や後続の子を捨てない。宣言、capture bindings、local demands、子の完全な再帰treeを保持し、各nodeのunsupportedとrigid rejectは分ける。

新規 `CommonRoleGuardedIntervalFrontier` は212行、10公開定理。前回の次候補 `guarded_plan_frontier` の情報保持とモデル対応の部分目標を閉じた。全B4は未達で、主要橋は5本のまま。静的な有限treeを、更新が安定した後の言語の4分類とは呼ばない。

## 正確な量化と定理

以下はすべて `Yulang.CommonRoleGuardedIntervalFrontier`。

- `build_root`: 任意Checked registry、slots、Sources、goalで、計算treeのrootは元goal。
- `build_plans`: 同じ任意入力で、treeから消去したplanリストはcycle91 compileのplanリストと等しい。順序・重複を含む完全なリスト等式。単なるモデル集合の一致ではない。
- `accepted_retained`: 任意上記入力、任意registry所属declarationと独立Acceptsを満たすbindingsで、そのdeclaration、bindings、正確なlocal demands、**正確な全再帰child list**のbranchがtreeに存在し、child root列は元expand列に等しい。子の成功やモデルの存在は前提にない。
- `branch_sound`: 任意実buildのbranch所属に対し、そのdeclarationのregistry所属と独立Acceptsを返す。
- `branch_payload_exact`: 任意実buildのbranch所属に対し、local demandsが実capture生成と等しく、child listが全expand要素からの再帰buildと等しく、root列がexpandと等しい。
- `outside_exact`: 任意実buildのnodeとdeclarationで、outside所属とregistry所属かつinspect=noneがiff。
- `rejects_exact`: 同様にrejects所属とregistry所属かつ独立Rejectsがiff。unsupportedとは別。
- `ordinary_models_exact`: 任意Checked registry/slots/Sources/old/goal/assignmentで、treeのcomplete planから実生成したordinary atom列のどれかがAllを満たすことと、ある一つのsource valuationがoldと独立Derives全体を満たすことがiff。
- `run_exact`: 任意registry/slots/Sources/goal/treeで、実runがtreeを返すことと、あるChecked proofでtreeが実buildと等しいことがiff。runはcheckerを計算する。
- `run_models_exact`: 任意registry/slots/Sources/old/goal/assignmentで、runの返すtreeにordinaryモデルがあることと、Checkedかつ一つのsource valuationがoldと独立Derivesを満たすことがiff。callerのChecked、fuel、child-success、有限visit列、モデル存在の仮定はない。

独立Derivesはcycle91のregistry所属、独立Accepts、元HeadFits、同じvaluationでの全child導出をそのまま用いる。treeやplansの所属で宣言的意味を定義していない。全親/兄弟/oldのdemandsを一つの実generateへ渡すため、共有sourceの衝突を失わない。健全性・完全性はこの明示した静的断片のモデル対応だけ。新しい主型性定理ではない。

## 境界

- endpointは固定Form syntax。stateの絞り込み、再materialization、兄弟再訪、K2は扱わない。
- `Sources = Goal → Declaration → Nat → Nat` はcaller入力のまま。同じtupleの反復occurrenceはaliasする制限を引き継ぐ。invocationのfreshnessや共有寿命を決定していない。
- registry、goal、slots、old demandsの実sourceからの導出も未完。I-13台帳ACに追記した。
- public Treeは任意に構築できる。定理は実build/runの出力を対象とする。任意の手作りtreeの正当性は主張しない。
- nodeごとにaccepted/outside/rejectsの各listの順序と重複を保持する。3分類を横断した元registryの交互配置は保存していない。
- complete-plan消去は失敗したbranchを除くが、元treeには残る。plan数0や複数を言語のrejected/ambiguousへ写していない。
- declaration自体は保持するが、dictionary構築・観察同値・最終選択は未証明。
- 全treeをflattenしたoutside列とcycle91 boundariesのリスト等式は未証明。今回のoutside_exactは各実build nodeについての定理。

## 検証

以下は最終production Leanに対してexit 0。

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleGuardedIntervalFrontier --wfail
✔ [308/308] Built Yulang.CommonRoleGuardedIntervalFrontier (1.3s)
Build completed successfully (308 jobs).
ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang92/boundary-check.lean
exit 0, no diagnostics
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang92/axioms.lean
'Yulang.CommonRoleGuardedIntervalFrontier.build_root' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGuardedIntervalFrontier.build_plans' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGuardedIntervalFrontier.accepted_retained' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGuardedIntervalFrontier.branch_sound' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGuardedIntervalFrontier.branch_payload_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGuardedIntervalFrontier.outside_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGuardedIntervalFrontier.rejects_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGuardedIntervalFrontier.ordinary_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleGuardedIntervalFrontier.run_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGuardedIntervalFrontier.run_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

boundary-checkは**18個の#guardによる実行検査**と、共有source衝突についてのkernel proofを含む。#guard検査そのものをkernelで証明した定理とは呼ばない。missing first childの後のunsupported child、片方欠落、空registryと子0個leafの違い、duplicate宣言/childの順序・多重度、成功/失敗する親候補の混在、rigid mismatchとoutsideの違い、無関係な不正宣言、深さ8の成功/失敗、共有source衝突を検査した。最後の証明は実frontierのerasureを用いて、該当atom列を満たすassignmentが存在しないことを示す。

最初の直接 `decide +kernel` によるTree計算検査は、複合tupleのinstance-size制限とwell-founded tree reductionで止まった。期待値は変更せず、instance budgetを増やし、計算検査を#guardに分けた。意味的反駁は既存planへの証明済み消去を通してkernel検査した。型classや計算検査の失敗をモデルの反例として扱っていない。

```text
python3 tools/boundary-input-inventory.py --check
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=259; Main=93; Audit=259; ledger mentioned=132. Mention counts are not audit completion counts.
verify-lean: . @ f69125e29 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

`git diff --check`もexit 0。上記verifyはdiff-onlyで、全体build/全Audit/AxiomGateのPASSではない。全体のローカル検証は指示どおり実行していない。10定理の依存公理はpropext/Quot.sound、モデル対応では加えてClassical.choiceだけ。

## 公開と独立review

source commit: `8d32d32ce69958fd3ac4dcce097409ee972ad302`。
local checkpoint: `f69125e29`。
公開tree: `d1063f47dfcd20c0e581b996ee421f73544857bc`。

全9変更pathのblob SHAをローカルhash-objectと照合し、取得した非truncated tree（2,334 entries）も全path一致。全tree SHAがlocal checkpointのtreeと完全一致した。work/dots-mainだけに、live treeからSHA-only treeを作り、expected head + 非force更新で公開した。

source SHAのCI: Core CIはcompleted/success（https://github.com/momota1029/yulang/actions/runs/42873255045）。Lean inference kernelは報告準備中の取得時点でin_progress（https://github.com/momota1029/yulang/actions/runs/42873255543）。全CI成功はまだ主張しない。後続結果が得られた場合は追記する。

読み取り専用reviewerは独立Derivesとshared valuationの対応を確認。初回に「child rootsの等式だけでは設計が要求するfull child listの等式より弱い」と指摘したため、accepted_retainedを強化しbranch_payload_exactを追加した。最終コードと全boundary scriptの再reviewでblockerなし。reviewer自身はbuild/testを実行していない。回帰script全文を末尾に公開する。

## 残る主要橋と次の候補

B4への主要橋は5本のまま。
1. `source_boundary_adequate`: parser/declからscope、grouped clause、associated annotation、source occurrence/invocationを実際に導く。
2. `generated_work_closed`: state-dependent materialization後の一般childを計算された有限source-template領域に接続する。
3. `saturate_terminates_and_closes`: 兄弟更新/再生成を安定まで回すPaterson/K2 driver。
4. `saturated_frontier_exact`: 今回の静的unfinished treeを実飽和へ接続し、安定後の独立4分類を得る。
5. `resolve_dictionary_order_sound`: 正準source obligation順でのdictionary観察同値。

次の候補は (a) Form区間と実ordinary state materialization carrierを定義して接続する、(b) frontierの全再帰boundary抽出と独立Reachの対応、(c) 未完成treeをstate更新で再計算しても元source ownerと子結果を失わない橋。固定例や補助定理の本数を主定理の完了に数えない。

新規意味論判断0件、新規質問0件。既存のinvocation/非線形head等の未回答事項を維持した。新規Yulang2実行はなし。spec 6.3の兄弟連言/安定後最終化と、inboxの未完成診断treeの回答を根拠にしたが、今回の一般treeを実機照合したとは言わない。

## 復旧・時間・資源

- 開始2026-11-10T17:58:10Z。live integration/work双方5bf82f48を取得しstanding orders/inboxを再読、ACTIVEを確認。前cycle91 completed heartbeatとreportあり。別writer/buildなし。
- ローカル枝はcycle91のlocal/remote並行履歴だったためff-only取り込みは不可。tree差分0を確認して通常merge（25887d4ae）でintegrationを祖先に取り込んだ。既存成果の削除なし。
- 再接続通知後に状態を再確認。workspace、証明、ログが残り、別writer/buildもなく、live workは開始heartbeatと一致していた。公開helperの一時メモリは失われていたため再ロードした。未確定のremote writeや二重publicationはなかった。
- start heartbeat 6f63b364、約10分heartbeat 2da3fc15、source8d32d32c。18:15までに中間公開とtree照合が完了した。
- 新規clone/build cacheなし。同じworkspaceを継続。空きは開始48G/63G（使用13G）、終了overlay          63G   13G   48G  22% /workspace/scratch/1d0b4aaa3394。使用量の枠は不明。
- 9 source/heartbeat path + 最終reportの計10path。reportとcompleted heartbeatは公開後に再照合する。未公開production Leanはない。
- 初期elaborationではnested Tree recursionのsize減少、list map congruence、dependent subtype equalityを直した。既存定義/定理/期待値は変更していない。
- ログ: `../cache/yulang92`。この報告に回帰scriptを同梱。期限2026-11-10T18:22:19Z。

報告作成: 2026-11-10T18:16:28Z。経過18.3分。

## 再実行用回帰script全文

```lean
import Yulang.CommonRoleGuardedIntervalFrontier
import Yulang.CommonRoleRecursiveConflicts
open Yulang
open CommonRoleCaptureNormalization (Form)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleGuardedIntervalFrontier
namespace Cycle92BoundaryCheck
set_option maxRecDepth 8192
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 4000000

def mk (role : Nat) (lo hi : Form) : Goal := ⟨role, [(lo,hi)]⟩
def parent : Declaration := ⟨0,0,[.tick (.var 0)],[(1,[.var 0]),(2,[.var 0])]⟩
def left : Declaration := ⟨1,1,[.var 0],[]⟩
def right : Declaration := ⟨2,2,[.var 0],[]⟩
def sources : CommonRoleGuardedIntervalPlans.Sources := fun _ _ binder => binder
def goal := mk 0 (.tick .int) (.tick .int)
def shape (tree : Tree Nat) :=
  ((branches tree).map (fun e => e.1.key),
   (branches tree).map (fun e => e.2.2.2.map fun t =>
     ((root t).role, (branches t).length, (outside t).length, (plans t).length)),
   (outside tree).map (·.key), (rejects tree).map (·.key), (plans tree).length)
def summarize (ds : List Declaration) (g : Goal) := (run ds id sources g).map shape
#guard summarize [parent,left,right] goal = some ([0],[[(1,1,0,1),(2,1,0,1)]],[],[1,2],1)
#guard summarize [parent,left] goal = some ([0],[[(1,1,0,1),(2,0,0,0)]],[],[1],0)
#guard summarize [parent,right] goal = some ([0],[[(1,0,0,0),(2,1,0,1)]],[],[2],0)
#guard summarize [] goal = some ([],[],[],[],0)
#guard summarize [left] (mk 1 .int .int) = some ([1],[[]],[],[],1)
#guard summarize [parent,left,left,right] goal = some ([0],[[(1,2,0,2),(2,1,0,1)]],[],[1,1,2],2)
#guard summarize [parent,parent,left,right] goal = some ([0,0],[[(1,1,0,1),(2,1,0,1)],[(1,1,0,1),(2,1,0,1)]],[],[1,2],2)

def rigidRight : Declaration := ⟨2,3,[.tick (.var 0)],[]⟩
-- A missing first child does not discard the later unsupported child.
#guard summarize [parent,rigidRight] (mk 0 (.tick (.var 7)) (.tick (.var 7))) =
  some ([0],[[(1,0,0,0),(2,0,1,0)]],[],[3],0)
#guard summarize [rigidRight] (mk 2 .int .int) = some ([],[],[],[3],0)
#guard summarize [rigidRight] (mk 2 (.var 7) (.var 7)) = some ([],[],[3],[],0)

def terminalParent : Declaration := ⟨0,4,[.tick (.var 0)],[]⟩
#guard summarize [parent,terminalParent,left] goal =
  some ([0,4],[[(1,1,0,1),(2,0,0,0)],[]],[],[1],1)

def duplicateChild : Declaration := ⟨0,5,[.tick (.var 0)],[(1,[.var 0]),(1,[.var 0])]⟩
#guard summarize [duplicateChild,left] goal = some ([5],[[(1,1,0,1),(1,1,0,1)]],[],[1],1)

def reversed : Declaration := ⟨0,6,[.tick (.var 0)],[(2,[.var 0]),(1,[.var 0])]⟩
#guard summarize [reversed,left,right] goal = some ([6],[[(2,1,0,1),(1,1,0,1)]],[],[1,2],1)

def growing : Declaration := ⟨0,7,[.var 0],[(0,[.tick (.var 0)])]⟩
#guard (run [growing] (id : Nat → Nat) sources goal).isNone = true
#guard (run [parent,left,right,growing] (id : Nat → Nat) sources goal).isNone = true

def recursive : Declaration := ⟨0,8,[.tick (.var 0)],[(0,[.var 0])]⟩
def terminal : Declaration := ⟨0,9,[.int],[]⟩
def tower : Nat → Form | 0 => .int | n+1 => .tick (tower n)
#guard (run [recursive,terminal] (id : Nat → Nat) sources (mk 0 (tower 8) (tower 8))).map
  (fun t => (ordinary [] t).map List.length) = some [64]
#guard (run [recursive] (id : Nat → Nat) sources (mk 0 (tower 8) (tower 8))).map
  (fun t => ((branches t).length,(plans t).length)) = some (1,0)

-- A retained complete shape need not have an ordinary model.
def differentParent : Declaration := ⟨0,10,[.tick (.pair (.var 0) (.var 1))],[(1,[.var 0]),(2,[.var 1])]⟩
def differentGoal := mk 0 (.tick (.pair .int (.tick .int))) (.tick (.pair .int (.tick .int)))
def aliasSources : CommonRoleGuardedIntervalPlans.Sources := fun _ d binder => if d.key = 10 then binder else 2
def conflict : PresenceNormalForm.Atom Nat → Bool
  | .tyLe l r => CommonRoleRecursiveConflicts.check l r
  | .rowLe _ _ => false
def conflicting := run [differentParent,left,right] (id : Nat → Nat) aliasSources differentGoal
#guard conflicting.map (fun t => ((branches t).length, (ordinary [] t).map (fun a => a.any conflict))) =
  some (1,[true])

theorem conflict_refutes (atoms : List (PresenceNormalForm.Atom Nat))
    (found : atoms.any conflict = true)
    (assignment : Nat → Core.PresenceGeneration.Comp Common.model) :
    ¬ PresenceNormalForm.All Common.model assignment atoms := by
  obtain ⟨atom, member, hit⟩ := List.any_eq_true.mp found
  intro models
  have holds := models atom member
  cases atom with
  | tyLe l r => exact CommonRoleRecursiveConflicts.checked_no_subtype l r hit assignment holds
  | rowLe l r => cases hit
example (tree) (returned : conflicting = some tree)
    (atoms : List (PresenceNormalForm.Atom Nat)) (member : atoms ∈ ordinary [] tree)
    (assignment : Nat → Core.PresenceGeneration.Comp Common.model) :
    ¬ PresenceNormalForm.All Common.model assignment atoms := by
  obtain ⟨checked, rfl⟩ := (run_exact ..).mp returned
  have erased : ordinary [] (build [differentParent,left,right] checked id aliasSources differentGoal) =
      CommonRoleGuardedIntervalPlans.ordinary [differentParent,left,right] checked id aliasSources [] differentGoal := by
    simp only [ordinary, build_plans, CommonRoleGuardedIntervalPlans.ordinary]
  rw [erased] at member
  have computed : (CommonRoleGuardedIntervalPlans.run [differentParent,left,right]
      (id : Nat → Nat) aliasSources [] differentGoal).map
      (fun output => output.1.map (fun atoms => atoms.any conflict)) = some [true] := by decide +kernel
  have flags : (CommonRoleGuardedIntervalPlans.ordinary [differentParent,left,right] checked
      id aliasSources [] differentGoal).map (fun atoms => atoms.any conflict) = [true] := by
    simpa [CommonRoleGuardedIntervalPlans.run, List.all_eq_true.mpr checked] using computed
  have hit : atoms.any conflict ∈ (CommonRoleGuardedIntervalPlans.ordinary
      [differentParent,left,right] checked id aliasSources [] differentGoal).map
        (fun a => a.any conflict) := List.mem_map.mpr ⟨atoms,member,rfl⟩
  rw [flags] at hit
  exact conflict_refutes atoms (List.mem_singleton.mp hit) assignment
end Cycle92BoundaryCheck
```

## Exact-source CIの完了追記（2026-11-10T18:17:56Z）

source `8d32d32ce69958fd3ac4dcce097409ee972ad302` のCore CIとLean inference kernelは、両方completed/successを確認した。
- Core: https://github.com/momota1029/yulang/actions/runs/42873255045
- Lean: https://github.com/momota1029/yulang/actions/runs/42873255543

Lean proof jobのLean action、全宣言Audit、source/value/regular/semantic-record examplesも全てsuccess。これはremote CIの結果であり、ローカル全体検証とは区別する。source公開後にproduction Leanは変更していない。報告/heartbeatだけの最終commitのCIとは区別する。

最終公開準備時点の経過19.8分。時間を埋める定理は追加していない。
