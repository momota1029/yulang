# dots cycle 94 — 保持したfrontierから実ordinary graphへの接続

## 結果と部分目標

**固定区間の実診断treeが持つ全complete planを、実ordinary constraint graphへ接続し、元のtype/row assignmentごとの正確な対応を閉じた。** 既存ordinary atomsとold demandsを全て保持し、各宣言の選択肢は別graphにする。tree自体は変えないので、未完成childやunsupported診断はgraphが0本の場合も失われない。

新規 `CommonRoleFrontierGraphs` は143行、9公開定理。部分目標は閉じた。ただしこれはgraph生成と意味保存の橋であり、普通solverの実行、stateからのForm再生成、飽和、安定後4分類ではない。**B4主定理には主要橋が5本残る。**

## 正確な量化と主張

以下の定理は全て `Yulang.CommonRoleFrontierGraphs`。

1. `graph_count`: 任意n/既存atoms/old demands/treeで、計算したgraphの本数はtreeのcomplete plan数と等しい。整合性とは無関係。
2. `graphs_exact`: 同じ任意入力と元assignmentで、graph familyのどれかがそのassignmentをliteral readbackするモデルを持つことと、既存atomsかつtreeのordinary alternativeをそのassignmentが満たすことがiff。
3. `build_models_exact`: 任意Checked registry、slots、Sources、既存atoms、old、goal、assignmentで、実buildからのgraph familyの表現と、既存atomsかつ一つの共有source valuationによるold/独立Derivesがiff。
4. `run_models_exact`: 任意同入力（Checked証明は不要）で、public runの出力graphに元assignmentを表すモデルがあることと、Checkedかつ既存atomsかつ一つの共有source valuationによるold/独立Derivesがiff。
5. `run_tree_exact`: 任意public入力で、出力のtree射影は既存frontier.runと等しい。graph生成は診断treeを変更しない。
6. `graph_reflects`: 任意public実行結果、そのgraph familyの任意graph、その任意rows/valuesモデルで、readbackはChecked、既存atoms、oldと独立Derivesの共有sourceモデルを満たす。compilerが選んだ特別なモデルだけではない。
7. `graph_input_injective`: 任意treeから生成した任意graphで、元Fin n inputのallocationは単射。内部ノードの追加で元slotを併合しない。
8. `advance_exact`: 任意tree/old/既存atoms/fresh atoms/assignmentで、freshを加えて再compileしたfamilyの表現は、旧familyの表現かつfreshを満たすこととiff。
9. `advance_replays`: freshを加えた任意graphの任意モデルは、元type/row readbackが完全に同じ旧familyのgraphモデルへ戻せる。内部ノード数/番号が等しいとは言わない。

Derivesは以前の独立な有限宣言導出であり、新graphの所属やモデルをその定義に使わない。graph Modelsは既存compilerの定義、edge、rowの独立解釈。全体に一つのsource valuationを置くので兄弟別の矛盾するモデルを別々に採用しない。

## 明示的な境界

- **整合しないcomplete planもgraphを作る。** graphがあることと、モデルがあること/solver成功は異なる。空familyを最終拒否分類にしていない。
- 原型Formのsyntax treeは固定。fresh atomsを加えてもinspect/childrenは再計算しない。`advance_exact`をstate materializationや飽和の完成と呼ばない。
- registry/goal/slots/Sourcesは引き続きcaller入力。同じgoal/declaration/binder tupleのalias制約を継承する。parserからのscope/source導出、invocation lifetime、辞書観察は未達。
- 既存atomsは任意で、grammar certificateや整合性の前提はない。これはgraph compilerの全域性であり、全てのFormを既存Boolean ordinary solverが決定するという主張ではない。
- graphごとに内部sizeは異なり得る。readbackによる元の値とrowの一致だけを保証する。任意rowを保持し、pure rowへ置き換えない。
- 新意味論判断0件、新質問0件。I-13台帳AEに入力と未達を記録した。既存Lean定義/定理/spec/lakefileは変更していない。

## 検証

最終production Leanに対して次を実行し、全てexit 0。

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleFrontierGraphs --wfail
✔ [310/310] Built Yulang.CommonRoleFrontierGraphs (1.2s)
Build completed successfully (310 jobs).
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang94/boundary-check.lean
exit 0, no diagnostics
ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang94/axioms.lean
'Yulang.CommonRoleFrontierGraphs.graph_count' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierGraphs.graphs_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierGraphs.build_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFrontierGraphs.run_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFrontierGraphs.run_tree_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierGraphs.graph_reflects' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFrontierGraphs.graph_input_injective' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierGraphs.advance_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFrontierGraphs.advance_replays' depends on axioms: [propext, Quot.sound]
```

13個の#guardと4個のkernel検査付きexample。空registry、leaf、全child成功、missing/unsupported child保持、duplicate親/childのplan積、矛盾する旧ordinary atomsでもgraphは残ること、row制約の元index、input単射、origin生成、不正宣言によるglobal checker拒否を検査した。

kernel exampleでは、矛盾する既存atoms/fresh atomsが全graphモデルを排除すること、任意rowのliteral保持、後stateから旧stateへの元readbackが同一であることを確認した。#guardをkernelで証明した定理とは呼ばない。期待値の変更なし。

```text
python3 tools/boundary-input-inventory.py --check
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=261; Main=93; Audit=261; ledger mentioned=134. Mention counts are not audit completion counts.
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: . @ c958d5e6c (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

`git diff --check`もexit 0。全ローカルbuild、全Audit、全AxiomGateは常設指示どおり未実行。verifyはdiff-onlyのPASS。今回9定理の公理はpropext/Classical.choice/Quot.soundの範囲。

初回elaborationはpublic output tupleの型推論とOption mapの関数合成の2箇所が未解決だった。出力tupleを明示し、合成を展開して修正した。修正後のtrust-zero再check、focused build、回帰、公理検査が通った。別reviewerはthread上限で起動できなかったため、独立review済みとは言わない。自己reviewでは量化、旧state保存、graph/modelの区別と固定syntax境界を確認した。

## 公開

source commit: `33c0b508c84d732326184ab71fdb2cf1a73fcf39`。
local checkpoint: `c958d5e6cd610b234f877731f40bbfd076bf3c6e`。
source tree: `d6f83cfc4fac0f57de9ec903884792d5ae936df2`。

9変更pathを個別blobで作成し、返却SHAはすべてlocal hash-objectに一致。
live work/dots-mainのtreeをbaseにSHA-only treeを作成し、全tree SHAがlocal treeと等しいことを確認した。非force・expected-head更新後、refを再読してsource commit一致、非truncatedのrecursive tree（2340 entries）と9変更pathの全blob SHA一致を確認した。他pathを保持している。

報告と最終心拍を含む今回の変更は10path。CIの最終確認結果と最終公開照合は後述。

## B4に残る5橋と次の候補

1. `source_boundary_adequate`: parser/declからscope、annotation、source occurrence/invocationを実導出。
2. `generated_work_closed`: state依存で再materializeした一般childを計算済み有限source-template領域へ接続。
3. `saturate_terminates_and_closes`: 兄弟更新と再生成を安定まで回すPaterson/K2 driver。
4. `saturated_frontier_exact`: 実飽和に接続した安定後の独立4分類。
5. `resolve_dictionary_order_sound`: 正準source obligation順のdictionary観察同値。

次の候補は(a) source interval Formをordinary stateから取り出す実materialization境界、(b) 制約が強くなるときの再inspectと有限work閉包、(c) graph familyを実ordinary solverへ渡せるgrammar範囲の明示とchecker。今回のgraph生成だけをsolver成功と数えない。

## 復旧・時間・資源

開始2026-11-10T18:58:27Z、期限19:22:19Z。live integration/workは共にb1cc63ec。standing orders/inboxをlive取得して再読し、ACTIVE・上限なしを確認した。前cycle93 completed心拍/報告あり、前writerもLean/Lake processもなし。通常再開でcrash recoveryなし。

既存workspace/cache一つを使用。integrationを通常mergeし、local treeがlive integration treeと完全一致することを確認した。新clone/cacheコピーなし。開始/終了とも63G中13G使用・48G空き。使用量の枠は不明。

startup heartbeatはfc5e8e84。ログは../cache/yulang94。公開manifestの最初のローカル読込が出力長で切れたため、小さいchunkで読み直して全JSONを復元してからblobを作った。GitHub書込み拒否/不確定の再試行ではなく、local転送の読込制限だった。時間埋め用の定理は追加していない。

報告準備: 2026-11-10T19:08:25.532157+00:00、経過10.0分。

## 再実行用の回帰script

```lean
import Yulang.CommonRoleFrontierGraphs
open Yulang
open CommonRoleCaptureNormalization (Form)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleGuardedIntervalPlans (Sources Plan)
open CommonRoleGuardedIntervalFrontier (Tree)
open CommonRoleFrontierGraphs
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom All)
namespace Cycle94BoundaryCheck
set_option maxRecDepth 8192
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 4000000

def mk (role : Nat) (form : Form) : Goal := ⟨role,[(form,form)]⟩
def parent : Declaration := ⟨0,0,[.tick (.var 0)],[(1,[.var 0]),(2,[.var 0])]⟩
def left : Declaration := ⟨1,1,[.var 0],[]⟩
def right : Declaration := ⟨2,2,[.var 0],[]⟩
def rigidRight : Declaration := ⟨2,3,[.tick (.var 0)],[]⟩
def sources : Sources := fun _ _ binder => binder
def slots : Nat → Fin 2 := fun n => ⟨n % 2, Nat.mod_lt n (by decide)⟩
def goal := mk 0 (.tick .int)
def unknownGoal := mk 0 (.tick (.var 7))
def bad : List (Atom (Fin 2)) := [.tyLe (.base .int) (.base .str)]
def rowsOnly : List (Atom (Fin 2)) := [.rowLe (.var 0) (.var 1),.rowLe (.var 1) (.var 0)]
def summary (ds : List Declaration) (g : Goal) (existing : List (Atom (Fin 2)) := []) :=
  (run ds slots sources existing [] g).map fun output =>
    ((CommonRoleFrontierReachability.goals output.1).map (·.role),
      (CommonRoleFrontierReachability.boundaries output.1).map (fun e => (e.1.role,e.2.key)),
      output.2.length)

#guard summary [] goal = some ([0],[],0)
#guard summary [left] (mk 1 .int) = some ([1],[],1)
#guard summary [parent,left,right] goal = some ([0,1,2],[],1)
-- The graph compiler does not treat a contradictory state as no structural plan.
#guard summary [parent,left,right] goal bad = some ([0,1,2],[],1)
-- No complete graph is available, but all missing/unsupported descendants remain.
#guard summary [parent,rigidRight] unknownGoal = some ([0,1,2],[(2,3)],0)
#guard summary [parent,parent,rigidRight] unknownGoal = some ([0,1,2,1,2],[(2,3),(2,3)],0)
-- Distinct alternatives and duplicate declarations are not conjoined or deduplicated.
#guard summary [parent,parent,left,right] goal = some ([0,1,2,1,2],[],2)
#guard summary [parent,left,left,right,right] goal = some ([0,1,2],[],4)
-- Row inequalities survive, with the original source-slot indices.
#guard (run [parent,left,right] slots sources rowsOnly [] goal).map
  (fun o => o.2.map (fun g => g.rows.length)) = some [2]
#guard (run [parent,left,right] slots sources rowsOnly [] goal).map
  (fun o => o.2.map (fun g => g.rows.map (fun pair =>
    match pair with
    | (.var first,.var last) => (first.val,last.val)
    | _ => (99,99)))) = some [[(0,1),(1,0)]]
-- Original input slots remain distinct even if the goal is closed.
#guard (run [left] slots sources [] [] (mk 1 .int)).map
  (fun o => o.2.map (fun g => g.input (0 : Fin 2) != g.input (1 : Fin 2))) = some [true]
-- Independent graph interpretation is available without a chosen semantic model.
#guard (run [parent,left,right] slots sources [] [] goal).map
  (fun o => o.2.map (fun g => g.origin.isSome)) = some [true]
-- A malformed declaration anywhere still rejects the complete registry.
def growing : Declaration := ⟨8,8,[.var 0],[(8,[.tick (.var 0)])]⟩
#guard (run [parent,left,right,growing] slots sources [] [] goal).isNone = true

-- A nonempty structural graph family can have no represented assignment.
example (old : Plan (Fin 2)) (tree : Tree (Fin 2)) (assignment : Fin 2 → Comp Common.model) :
    ¬ Represents (graphs bad old tree) assignment := by
  intro represented
  have prior := ((graphs_exact bad old tree assignment).mp represented).1
  have wrong := prior (.tyLe (.base .int) (.base .str)) (by simp [bad])
  change Common.Subtype (.base .int) (.base .str) at wrong
  have impossible := (CommonRigidHeadInspection.base_iff _ _).mp wrong
  cases impossible

-- Readback preserves arbitrary original rows, not only pure assignments.
example (g : CommonPresenceConstraintGraph.Compiled n) (rows : Fin n → Common.Row)
    (values : Fin g.size → Common.Ty) (i : Fin n) :
    (g.readback rows values i).2 = rows i := rfl

-- Appended contradictory ordinary constraints eliminate all models, but do not
-- alter the tree or the number/order of compiled plans.
example (old : Plan (Fin 2)) (tree : Tree (Fin 2))
    (existing : List (Atom (Fin 2))) (assignment : Fin 2 → Comp Common.model) :
    ¬ Represents (graphs (existing ++ bad) old tree) assignment := by
  intro represented
  have prior := ((advance_exact existing bad old tree assignment).mp represented).2
  have wrong := prior (.tyLe (.base .int) (.base .str)) (by simp [bad])
  change Common.Subtype (.base .int) (.base .str) at wrong
  have impossible := (CommonRigidHeadInspection.base_iff _ _).mp wrong
  cases impossible

-- Replay means exact original readback, not graph-index equality.
example (existing fresh : List (Atom (Fin n))) (old : Plan (Fin n))
    (tree : Tree (Fin n)) (g : CommonPresenceConstraintGraph.Compiled n)
    (member : g ∈ graphs (existing ++ fresh) old tree) (rows : Fin n → Common.Row)
    (values : Fin g.size → Common.Ty) (models : g.Models rows values) :
    ∃ oldGraph ∈ graphs existing old tree, ∃ oldValues,
      oldGraph.Models rows oldValues ∧ oldGraph.readback rows oldValues = g.readback rows values :=
  advance_replays existing fresh old tree g member rows values models
end Cycle94BoundaryCheck
```

## Exact-source CIと最終公開準備（2026-11-10T19:08:50.020005+00:00）

source `33c0b508c84d732326184ab71fdb2cf1a73fcf39` に対するCore CIとLean inference kernelが
両方completed/success。Lean proof jobの全build、全宣言Audit、source/value/regular/semantic
record examplesもsuccess。remote CIの結果であり、ローカル全体検証とは区別する。
source公開後のproduction Leanの変更なし。

- Core: https://github.com/momota1029/yulang/actions/runs/42881966872
- Lean: https://github.com/momota1029/yulang/actions/runs/42881966950

約10.4分の完了心拍とこの報告を同じtreeで公開し、ref/tree/変更blobを照合する。
