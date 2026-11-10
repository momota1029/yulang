# dots cycle 98 — 累積ordinary制約の実solver検査とreplayの接続

## 結果と部分目標

**任意の有限なgrammar-valid追加batchについて、実ordinary solverで累積状態を検査し、成功が「全batchを同じ一つのassignmentで満たせる」と同値である入口を作った。その成功だけからChainを内部で証明し、cycle97のcached診断replayのsource上限と、毎回新しいgraphを返す入口へ接続した。**

部分目標は閉じた。`CommonRoleCheckedOrdinaryReplay`は215行、13公開定理。
最初の状態も検査するため、batchが空でも初期矛盾を通さない。
個別には充足可能でも一緒には矛盾するbatchを、別々のassignmentで通すことはない。
空batch・重複batch・変わらない状態の後も、後続の型情報まで処理する。

source commit: `59f4a991e8eff0ed4cda6d466fcefb385231a593`。
source tree: `fd3645b018e321a169abd83fec0fb45668c03f60`。
ローカルsource commit `c4d9d36eb` と木全体が一致し、公開9pathのblobも取得して一致を確認した。

これは実solverに対する有限な追加batchの境界を閉じた結果であり、実ソースがbatchを生成すること、source/invocation identity、動的slot追加、飽和schedulerを完成した結果ではない。
**T1c全体、外側resolve_exact、X13〜X16の外側入口、B4の5橋は未完成。**

## 定理と量化・前提・側

以下は全て`Yulang.CommonRoleCheckedOrdinaryReplay`。
State nは既存のatom列とchild/width/rowの3grammar証明を持つ。
実行入口にmodel、Chain、checker証明、work boundを渡す必要はない。

1. `append_models`: 任意State、batch、単一assignmentについて、appendのモデル性 iff 元Stateとbatchの両方のモデル性。補助。
2. `final_atoms`: 任意初期Stateと有限batch列について、最終atomsは初期atomsと全batch atomsの順序付き連結に等しい。重複を保持する。補助。
3. `final_models`: 任意初期State、有限batch列、assignmentについて、最終状態のモデル性 iff 初期と全batchをその同じassignmentが満たす。局所健全性・完全性の補助。
4. `final_includes`: 任意初期Stateと有限batch列で、元の全atomは最終状態にもある。補助。
5. `final_models_initial`: 任意初期Stateと有限batch列で、最終状態にmodelがあれば初期状態にもある。補助。
6. `validate_exact`: 任意初期Stateと有限batch列で、実solver検査成功 iff 最終累積状態にCommon modelがある。局所健全性・完全性。
7. `validate_models`: 同じ任意入力で、検査成功 iff 一つのassignmentが初期atomsと全batchの全atomを満たす。独立した共有assignmentの連言への局所健全性・完全性。
8. `trace_length`: 任意初期Stateと有限batch列で、計算された更新後状態列の長さはbatch数。補助。
9. `validate_chain`: 任意初期Stateと有限batch列で、実検査が成功したなら、実計算した累積atom列がChainを満たす。modelや包含の前提をcallerに追加していない。補助。
10. `run_exact`: 任意registry、slots、Sources、元Goal、初期State、有限batch列、outputについて、public run成功 iff 最終ordinary状態にmodelがあり、checked registryが存在してoutputが実replayと等しい。局所健全性・完全性。
11. `run_none_iff`: 同じ任意public入力で、none iff 最終ordinary状態にmodelが無い、またはregistryがCheckedでない。宣言の不正とordinary矛盾は別の条件。局所健全性・完全性。
12. `run_computed_bound`: 任意成功public runについて、実workDomainが返すboundが存在し、snapshot数は1 + batch数、rebuild数は1 + 元Goalの変数出現数以下、再構築treeのpreorder出現数はその数×bound長以下。Chainを追加前提にしない。補助・進捗上限。
13. `run_graphs_exact`: 任意成功public runと任意の時点別old demandsについて、gated public runGraphsも成功し、全graph出力は全累積状態で直接呼んだ既存public materialized runの完全な出力列と等しい。補助・出力一致。

局所健全性・完全性は、この明示したfinite batch境界のiffである。
M1全体のTyping/inferの三つ組や主型性を証明したという主張ではない。

## 境界と未達

- 全batchは同じ固定Fin n上にあり、3つの既存grammar条件をcallerが満たす。実ソースからこれを導くこと、任意のunsupported atomを処理すること、新しいslotを確保することは未証明。
- 有限batch列はcaller入力。実schedulerがbatchを生成するadequacy・fairness・停止は未証明。snapshotの長さと実solver呼出し回数はbatch数に依存し、rebuild boundから制限できない。
- 元Goal、slots、Sourcesは固定。materializationは既存の明示paired-int evidence断片のまま。str/bool/unitを言語仕様として拒否するのではなく、materializationの対象外である。
- ordinary検査は実finite solver。成功時は初期状態と全累積状態を検査し、失敗時はList.allが短絡しうる。計算にmodel oracleはない。
- graphは各時点のatomsと独立したold demandsから再生成する。ordinary状態が充足可能でも、追加old demandsやrole planを含むgraphが充足可能とは限らない。guardで実際に矛盾するold demandを残している。
- `visits`は再構築treeの完全preorder出現数という会計尺度。ordinary solver、graph構築、全traversal、総runtimeの上限ではない。
- sole candidateを理由にhead等式を共有状態へcommitしていない。新しい言語意味論の選択0件、質問ノート0件。既存のsource/invocation identity質問は未解決のまま。

## 検証

最終production moduleに以下を実行した。全てexit 0。
全ローカルbuild、全Audit、全AxiomGate、全verify-leanは指示どおり未実行。

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleCheckedOrdinaryReplay --wfail
✔ [314/314] Built Yulang.CommonRoleCheckedOrdinaryReplay (958ms)
Build completed successfully (314 jobs).
exit 0
```

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang98/boundary-check.lean
exit 0
```

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang98/axioms.lean
'Yulang.CommonRoleCheckedOrdinaryReplay.append_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCheckedOrdinaryReplay.final_atoms' depends on axioms: [propext]
'Yulang.CommonRoleCheckedOrdinaryReplay.final_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCheckedOrdinaryReplay.final_includes' depends on axioms: [propext]
'Yulang.CommonRoleCheckedOrdinaryReplay.final_models_initial' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCheckedOrdinaryReplay.validate_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCheckedOrdinaryReplay.validate_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCheckedOrdinaryReplay.trace_length' depends on axioms: [propext]
'Yulang.CommonRoleCheckedOrdinaryReplay.validate_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCheckedOrdinaryReplay.run_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCheckedOrdinaryReplay.run_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCheckedOrdinaryReplay.run_computed_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCheckedOrdinaryReplay.run_graphs_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

```text
python3 tools/boundary-input-inventory.py --check
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=265; Main=93; Audit=265; ledger mentioned=138. Mention counts are not audit completion counts.
exit 0
```

```text
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: . @ c4d9d36eb (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
exit 0
```

31実行guardと5kernel example。初期矛盾・空batch・slot数0のvalidator、個別には可だが共同では矛盾するbatch、逆順矛盾、重複atoms、遅いevidence、2slot、非int、invalid registry、重複宣言・候補、非単射slotと反復変数を検査した。treeが同じままold demandsが空・矛盾・空となるgraph列と、後着のrow制約がgraphに残ることも確認した。

13定理の公理はpropext / Classical.choice / Quot.soundのみ。
`git diff --check`と`git diff --cached --check`はexit 0。
独立read-only reviewは最終module blob `5a36d36e2d1b421edb0b0dcbd3e3dec94feb38fc`、全13定理、regression source、scope文言を確認し、blocking issueなし。reviewer自身はbuild/auditを再実行していない。

最初のproduction buildは存在しないOptionの補題名で失敗し、casesによる証明へ直した。最初のregressionではAtom列の等号に計算用判定が無くguardにできなかったため、同じ等号をkernel exampleのrflで確認した。期待値や主張は弱めていない。inventoryの未対応オプションと、commit前のdiff gate失敗を直し、正規の生成方法・commit後のgateで再実行して成功した。

## Yulang2との照合

開始時にwork/dots-auditを取得し、x-oracleのX13〜X16を読んだ。
shared box、深さ2、同頭の局所区間、異頭の近似についての既存観測であり、一般の累積batch/schedulerの実機証明ではない。新しいYulang2実機実行なし。
spec6.3のordinary制約の連言、関連型等式を通した情報の流入、兄弟更新の安定前に最終化しない規則に従う。唯一implから型を決める規則を加えていない。

## 再開・公開・時間

- 開始: 2026-11-10T20:56:34Z。integration/m1-finalを取得し、最新standing ordersとinboxを再読。ACTIVE、上限なし。cycle97 completed、対応reportあり。復旧は不要。
- live APIとintegrationは`d38908669`。保持workspaceへintegrationをmergeし、cycle97の検証済み木を維持した。開始時にLean/Lake/Gitの前cycle processなし。native agent一覧でも他のYulang writerなし。
- 起動heartbeat: `c96fa94cde83073675a5e226cc47e23a4e7e9de2`。
- source途中公開: 21:07:31Zまでに`59f4a991`。8成果物とheartbeatの9path。個別blob作成→SHAのみtree→commit→非force expected-head ref更新。live treeを維持し、integrationへ書き込んでいない。
- 10分heartbeatは大きな既存Audit/README等の個別blob公開中に約1分遅れた。心拍のupdatedは準備時刻21:04:48Zで、公開時刻と混同しない。20分の途中公開期限より前にsourceを公開済み。
- 最終公開はreportとcompleted heartbeatの2path。sourceを含む異なるpathは合計10。最終ref/tree/blobを照合してから完了を報告する。
- 開始時・source公開後とも空き47G、clone追加・cacheコピー・データ削除なし。使用量の枠は不明。ログは`../cache/yulang98`。

## B4に残る5橋と次の候補

1. `source_boundary_adequate`: 実parser/declからscope、annotation、source/invocation、grammar-valid batchを導く。
2. `generated_work_closed`: 固定templateと明示int evidenceを一般の状態依存生成仕事へ接続する。
3. `saturate_terminates_and_closes`: sourceからbatchを生成し、ordinary更新の進捗とfairnessを示す実scheduler。今回の検査と再構築budgetだけでは無限のplateauや新atom追加は止まらない。
4. `saturated_frontier_exact`: 実飽和後と独立した最終4分類の接続。
5. `resolve_dictionary_order_sound`: 正準source義務順のdictionary観察同値。

次候補は、(a) 実関連型・capture生成からgrammar-valid追加batchへのprovenance付き入口、(b) 実ordinary仕事の有限領域・重複除去とfair scheduling、(c) 再訪source/invocation identityの仕様境界。未回答の意味論をcaller入力として隠し、B4完成とはしない。

## 再実行可能な境界回帰

```lean
import Yulang.CommonRoleCheckedOrdinaryReplay
open Yulang
open CommonRoleSettledConstraints (State)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleGuardedIntervalPlans (Sources Plan)
open CommonRoleCheckedOrdinaryReplay
open Core.PresenceGeneration (Comp TyTerm)
open PresenceNormalForm (Atom All)
namespace Cycle98BoundaryCheck
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 8000000

def slots : Nat → Fin 2 := fun n => ⟨n % 2, Nat.mod_lt n (by decide)⟩
def sources : Sources := fun _ _ binder => binder
def empty : State 2 := State.empty
def eqn (i : Fin 2) (base : Inference.Base) : State 2 :=
  CommonRoleCandidateStateFrontier.extend State.empty i base
def one := eqn 0 .int
def other := eqn 1 .int
def incompatible := eqn 0 .str
def bad := append one incompatible

def parent : Declaration := ⟨0,0,[.tick (.var 0)],[(1,[.var 0]),(2,[.var 0])]⟩
def left : Declaration := ⟨1,1,[.var 0],[]⟩
def right : Declaration := ⟨2,2,[.int],[]⟩
def growing : Declaration := ⟨9,9,[.var 0],[(9,[.tick (.var 0)])]⟩
def goal : Goal := ⟨0,[(.tick (.var 0),.tick (.var 0))]⟩
def scalarGoal : Goal := ⟨0,[(.var 0,.var 1)]⟩
def counts (registry : List Declaration) (g : Goal) (initial : State 2) (batches : List (State 2)) :=
  (run registry slots sources g initial batches).map fun r => (r.snapshots.length,r.rebuilds,r.visits)

#guard validate (State.empty : State 0) []
#guard validate empty []
#guard validate one []
#guard validate incompatible []
#guard !validate bad []
#guard !validate bad [empty,other]
#guard validate empty [one]
#guard validate empty [incompatible]
-- Each batch has a model, but they cannot choose separate assignments.
#guard !validate empty [one,incompatible]
#guard !validate empty [incompatible,one]
#guard validate empty [one,empty,one,other,empty]
#guard validate empty [other,one,empty]
example : (final empty [one,empty,one]).atoms = one.atoms ++ one.atoms := by rfl
#guard (trace empty [one,empty,one]).map (fun s => s.atoms.length) = [2,2,4]
#guard counts [parent,left,right] goal empty [] = some (1,1,3)
#guard counts [parent,left,right] goal empty [empty,empty,one,empty] = some (5,2,6)
#guard counts [parent,left,right] goal empty [empty,one,one,other] = some (5,2,6)
#guard counts [] scalarGoal empty [empty,one,one,other,empty] = some (6,3,3)
#guard counts [parent,left,right] goal one [one,other,empty] = some (4,1,3)
#guard counts [parent,left,right] goal empty [incompatible] = some (2,1,3)
#guard counts [parent,left,right] goal empty [eqn 0 .bool] = some (2,1,3)
#guard counts [parent,left,right] goal empty [eqn 0 .unit] = some (2,1,3)
#guard counts [parent,left,right] goal empty [one,incompatible] = none
#guard counts [parent,left,right] goal bad [] = none
#guard counts [parent,left,right,growing] goal empty [one] = none
#guard counts [parent,parent,left,right] goal empty [one,empty] = some (3,2,10)
#guard counts [] ⟨0,[(.pair (.var 0) (.tick (.join (.var 2) (.var 1))),.var 0)]⟩
  empty [one,other,empty] = some (4,3,3)
#guard counts [parent,left,right] goal empty [other] = some (2,1,3)

def emptyDecl : Declaration := ⟨1,1,[],[]⟩
def changingOld (i : Nat) : Plan (Fin 2) :=
  if i = 1 then [(99,(.base .int,.base .str))] else []
-- Graph constraints need not have a model just because ordinary atoms do.
#guard (runGraphs [emptyDecl] slots sources ⟨1,[]⟩ empty [empty,empty] changingOld).map
  (fun out => (out.1.rebuilds,out.2.map (fun pair => pair.2.map (fun graph => graph.edges.length)))) =
    some (1,[[0],[1],[0]])
#guard (runGraphs [emptyDecl] slots sources ⟨1,[]⟩ bad [] changingOld).isNone

def rowBatch : State 2 :=
  ⟨[.rowLe (.var 0) (.var 1)],
    (by intro atom member; simp only [List.mem_singleton] at member; subst atom; trivial),
    (by intro source target member; simp at member),
    (by intro atom member; simp only [List.mem_singleton] at member; subst atom; rfl)⟩
#guard validate one [rowBatch]
#guard (runGraphs [parent,left,right] slots sources goal one [rowBatch] (fun _ => [])).map
  (fun out => (out.1.rebuilds,out.2.map (fun pair => pair.2.map (fun graph => graph.rows.length)))) =
    some (1,[[0],[1]])

example (initial : State 2) (batches : List (State 2)) :
    validate initial batches = true ↔ ∃ assignment : Fin 2 → Comp Common.model,
      All Common.model assignment initial.atoms ∧ ∀ b ∈ batches, All Common.model assignment b.atoms :=
  validate_models initial batches

example (registry : List Declaration) (g : Goal) (initial : State 2) (batches : List (State 2))
    (out : CommonRoleFrontierReplay.Replay 2)
    (returned : run registry slots sources g initial batches = some out) :
    ∃ bound, CommonRoleStateMaterializedFrontier.workDomain registry g = some bound ∧
      out.snapshots.length = 1 + batches.length ∧
      out.rebuilds ≤ 1 + CommonRoleMaterializationProgress.potential g ∧
      out.visits ≤ (1 + CommonRoleMaterializationProgress.potential g) * bound.length :=
  run_computed_bound _ _ _ _ _ _ _ returned

example (initial : State 2) (batches : List (State 2))
    (valid : validate initial batches = true) :
    CommonRoleMaterializationProgress.Chain initial.atoms ((trace initial batches).map State.atoms) :=
  validate_chain initial batches valid

example (registry : List Declaration) (g : Goal) (initial : State 2) (batches : List (State 2)) :
    run registry slots sources g initial batches = none ↔
      ¬ (final initial batches).Models ∨ ¬ CommonRoleIntervalWorkClosure.Checked registry :=
  run_none_iff _ _ _ _ _ _
end Cycle98BoundaryCheck
```

報告準備時刻: 2026-11-10T21:09:48.005625+00:00. CIは下の追加節に実際の状態を記録する。


## Exact-source CI と最終公開準備

source `59f4a991e8eff0ed4cda6d466fcefb385231a593` のCore CIとLean inference
kernelは両方completed/success。production Leanの後続変更なし。
ローカルの全体検証を実施したという意味ではない。

- Core: https://github.com/momota1029/yulang/actions/runs/42901938017
- Lean: https://github.com/momota1029/yulang/actions/runs/42901938086

最終公開準備: 2026-11-10T21:10:06Z、経過13.5分。非force expected-head公開後に最終ref/tree/blobを照合する。
