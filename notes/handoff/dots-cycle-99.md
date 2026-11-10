# dots cycle 99 — 実ordinary evidence閉包からchecked replayへ

## 結果と部分目標

**既存の相互変数辺・scalar等式の有限閉包から、grammar検査済みのordinary追加batchを内部で計算し、実solver検査とcached診断replayへ接続した。callerが有限batch列を渡す境界を、この具体的な断片について取り除いた。**

部分目標は閉じた。新規`CommonRoleEvidenceReplay`は202行、18公開定理。
元のassignmentごとのモデル集合をそのまま保存し、独立なseed/transfer導出と
最終stateの明示的scalar等式が一致する。再計算でも新しいscalar factは出ない。
追加batch数は4*n以下、snapshot数は1+4*n以下。rebuildとvisitの既存source上限へ接続した。

source commit: `819bb1e77a8c3539ffae36636a4057f4cc68c2f4`。
source tree: `9256ed7b051b0f33c9840fec912dc56bfe67de48`。
ローカルsource commit `489489918` と木全体が一致。公開9pathのblob SHAを
取得したremote treeと照合し、全て一致した。

これは既存の有限scalar閉包を実ordinary更新に接続した結果であり、一般の
state-changing role schedulerの完成ではない。最初のordinary state、固定slot、
source/invocation mapはまだ入力。T1c全体、外側resolve_exact、X13〜X16の
外側入口、B4の5橋は未完成。

## 定理と量化・前提・側

以下はすべて`Yulang.CommonRoleEvidenceReplay`。各State nは既存の
child/width/row grammar証明を持つ。実行にmodel、Chain、fuel、batch列、
仕事領域、数値上限は渡さない。

1. `batch_models`: 任意fact=(slot,base)とassignmentについて、生成batchの全atomを満たす iff そのslotの型がbaseと同値。補助。
2. `completed_models`: 任意初期stateとassignmentについて、全生成batchを追加したstateの全atomを満たす iff 元stateの全atomを満たす。局所健全性・完全性。
3. `completed_models_iff`: 任意初期stateについて、生成後にmodelがある iff 元stateにmodelがある。局所健全性・完全性。
4. `validate_exact`: 任意初期stateについて、実ordinary solverによる生成trace検査が成功 iff 元stateにmodelがある。局所健全性・完全性。
5. `batches_length`: 任意初期stateについて、実生成batch数は実saturateのfact数。補助。
6. `batches_bounded`: 任意State nについて、実生成batch数は4*n以下。補助・有限進捗。
7. `evidence_stopped`: 任意初期stateについて、既存finite Hornの終了状態にfresh enabled scalar factは無い。実seed/transfer規則に限る。補助・閉包。
8. `completed_atoms`: 任意初期stateとatomについて、生成trace最終stateへの所属 iff 既存normalizeのstateへの所属。atom列の順序を同一視しない。補助。
9. `completed_evidence`: 任意初期state、slot、baseについて、生成後に明示的な両向きscalar等式がある iff 元stateから独立なDerivedが成り立つ。矛盾stateにも通る。局所健全性・完全性。
10. `derived_exposed`: 任意初期state、slot、baseについて、Derivedなら実生成後stateに両向き等式がある。局所完全性の補助。
11. `completed_linked`: 任意初期stateと2slotについて、生成後に相互変数辺がある iff 元stateにある。新しい変数辺を作らない。補助。
12. `completed_derived`: 任意初期stateとfactについて、生成後のDerived iff 元stateのDerived。局所健全性・完全性。
13. `completed_fixedpoint`: 任意初期stateとfactについて、生成後をsaturateしたfact所属 iff 元stateをsaturateした所属。列のidempotenceや重複atom削除ではない。補助・閉包。
14. `derived_detected`: 任意初期stateにmodelがあり、任意(slot,base)がDerivedなら、実生成後のdetectはそのbaseを返す。modelの前提は定理だけで、実行入力ではない。局所完全性の補助。
15. `run_exact`: 任意registry/slots/Sources/Goal/state/outputについて、実public runがoutputを返す iff 元stateにmodelがあり、Checked registryが存在し、outputは内部で生成したtraceの実replayそのもの。role成功を条件・結論にしない。局所健全性・完全性。
16. `run_none_iff`: 任意public入力について、none iff 元stateにmodelが無い、またはregistryがCheckedでない。局所健全性・完全性。
17. `run_computed_bound`: 任意成功public runについて、実workDomainが返すboundが存在し、snapshot数=1+実scalar fact数≤1+4*n、rebuild数≤1+元Goalの変数出現数、visit数≤その数×bound長。補助・有限進捗。
18. `run_graphs_exact`: 任意成功public runと時点別old demandsについて、public runGraphsも成功し、各graph出力は各実生成状態で既存public materialized runを直接呼んだ出力と一致する。補助・出力一致。

局所健全性・完全性は明示したseed/transfer scalar断片と実replay境界のiff。
M1全体のTyping/inferや主型性の三つ組の完成ではない。

## 境界と未達

- nとgrammar-certifiedな元stateはcaller入力。実parser/declからこれを導く橋、動的slot割当、source/invocation identityは未証明。
- batchは外から渡さず内部計算するが、scalar規則は元stateの明示的相互変数辺に固定。新しいassociated制約・辺・role childを生成する一般schedulerではない。
- `completed_evidence`は任意のordinary semantic entailmentの完全性ではない。一方向の変数辺から両向き等式を作らない。
- 既存saturateの結果列をbatchへ写す。内部Hornの発見順のtraceとは主張しない。全factは元stateのモデルが満たすため、この順序でもモデルを保存する。
- 二度目の実行でも新しいfactは出ないが、既存等式atomは再び追加され得る。回帰でこれを確認した。
- 4scalar baseのordinary等式を保持する。診断Formのmaterializationは既存のpaired-int断片のまま。str/bool/unitを言語仕様として拒否したわけではない。
- graph生成は各時点で更新され、old demandsとrowを保持する。ordinary modelがあることからgraphのmodelがあるとは言えない。空のgraph familyは最終言語分類でもない。
- visitは再構築treeの完全preorder出現数。総runtime、実solverの内部仕事、graph構築の上限ではない。
- sole candidateを理由にhead等式を共有stateへcommitしない。新しい意味論の選択0件、質問ノート0件。既存のidentity質問を回答済みにしていない。

## 検証

全て最終production moduleに対して実行、最終結果はexit 0。
指示どおり、ローカル全体build、全Audit、全AxiomGate、全verify-leanは実行していない。

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleEvidenceReplay --wfail
✔ [345/345] Built Yulang.CommonRoleEvidenceReplay (1.3s)
Build completed successfully (345 jobs).
exit 0
```

```text
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleEvidenceSaturationExamples --wfail
✔ [311/311] Built Yulang.CommonRoleEvidenceSaturationExamples (1.2s)
Build completed successfully (311 jobs).
exit 0
```

```text
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang99/boundary-check.lean
exit 0
```

```text
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang99/axioms.lean
'Yulang.CommonRoleEvidenceReplay.batch_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleEvidenceReplay.completed_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceReplay.completed_models_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceReplay.validate_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceReplay.batches_length' depends on axioms: [propext]
'Yulang.CommonRoleEvidenceReplay.batches_bounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceReplay.evidence_stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceReplay.completed_atoms' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleEvidenceReplay.completed_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceReplay.derived_exposed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceReplay.completed_linked' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleEvidenceReplay.completed_derived' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceReplay.completed_fixedpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceReplay.derived_detected' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceReplay.run_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceReplay.run_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceReplay.run_computed_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleEvidenceReplay.run_graphs_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

```text
python3 tools/boundary-input-inventory.py --check
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=266; Main=93; Audit=266; ledger mentioned=139. Mention counts are not audit completion counts.
exit 0
```

```text
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: . @ 489489918 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
exit 0
```

33実行guardと4kernel example。空state/slot0、seed無しcycle、多段相互辺、
4scalar base、衝突するseed、非相互の辺、invalid registry、重複宣言、row、
矛盾old demand、診断plateau、二度目の追加、証拠伝播前後の完全plan出現を検査。
18定理の公理はpropext / Classical.choice / Quot.soundのみ。
独立read-only reviewは最終module SHA256
`3bf26a19ec165b962e3444b697793ac81b058136dbf9b3fcebaa86651c7b96fb`
を確認し、run_exactを含めてblocking issueなし。reviewer自身はbuild/audit未実行。
`git diff --check`と`git diff --cached --check`もexit 0。

最初のmodule buildはmap内の存在量化の証明1箇所で失敗し、明示的な場合分けで修正。
最初の回帰は未buildの既存Examples importで失敗したため、そのmoduleだけbuildした。
次に単一辺のgrammar証明を修正し、rowテストのfixtureを修正した。元fixtureは
初期に完全planが無くgraph familyが空で、全時点に1graphという仮定が誤っていた。
row保持は常に完全な0-child宣言で確認し、元のParentは別guardで0→1→1→1の
plan出現を確認した。productionの定義、既存テストの期待値、主張は変更していない。

## Yulang2との照合

開始時にwork/dots-auditを取得してx-oracle X13〜X16を再読。
shared-box、深さ2、同頭の局所区間、異頭の近似の既存観測であり、一般scalar
schedulerの実機証明ではない。新しいYulang2実機実行なし。
spec6.3のordinary制約の連言と、等式を通した型情報の流入に沿う。
証明対象のscalar seed/相互辺規則は既存定義を再利用し、新しい規則を選んでいない。

## 再開・公開・時間

- 開始: 2026-11-10T21:28:27Z。date記録21:28:48Z。integration/workは双方8a4d9b74。最新standing orders/inboxを再読しACTIVE、上限なしを確認した。
- cycle98はcompletedとreportあり。保持workspaceへintegrationをmergeして再開。前cycleのLean/Lake/Git processと他のYulang writerは無く、復旧不要。
- 起動heartbeatは102afd99。source途中公開は819bb1e7、21:38:35Zまでに照合。個別blob→SHAのみtree→commit→非force expected-head更新。live treeを保存し、integrationへ書き込んでいない。
- sourceと一緒のheartbeatは開始10分の目安より約8秒遅れて公開した。updatedは準備時刻21:35:58Zであり、公開時刻とは区別する。20分前のsource途中公開を達成。
- source公開は8成果物とheartbeatの9path。最終report+completed heartbeatを追加し、異なるpathは合計10。最終ref/tree/blobを取得して照合後に完了を報告する。
- 開始時・source公開時とも空き47G。clone追加、cacheコピー、データ削除なし。使用量の枠は不明。ログは../cache/yulang99。

## B4に残る5橋と次の候補

1. source_boundary_adequate: 実parser/declからscope、annotation、source/invocation、grammar-validな元stateを導く。
2. generated_work_closed: 今回の固定scalar等式閉包を、一般の状態依存child/associated生成へ接続する。
3. saturate_terminates_and_closes: 新しいrole/ordinary仕事を生成する実schedulerの進捗とfairness。今回の有限scalar固定点だけでは閉じない。
4. saturated_frontier_exact: 実飽和後と独立した最終4分類の接続。
5. resolve_dictionary_order_sound: 正準source義務順のdictionary観察同値。

次候補は、(a) 実関連型生成とscalar再閉包の交互実行、(b) 実sourceに由来する
新しい相互辺の有限領域と重複除去、(c) 未回答のsource/invocation identity境界。
既存の全5橋は依然未完成だが、このscalar断片で外部batch列を仮定する必要は無くなった。

## 再実行可能な境界回帰

```lean
import Yulang.CommonRoleEvidenceReplay
import Yulang.CommonRoleEvidenceSaturationExamples
open Yulang
open CommonRoleSettledConstraints (State)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleGuardedIntervalPlans (Sources Plan)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom All)
open CommonRoleEvidenceReplay
namespace Cycle99BoundaryCheck
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 8000000

def slots : Nat → Fin 3 := fun n => ⟨n % 3, Nat.mod_lt n (by decide)⟩
def sources : Sources := fun _ _ binder => binder
def empty : State 3 := State.empty
def chain := CommonRoleEvidenceSaturationExamples.chain
def seed (base : Inference.Base) := CommonRoleCandidateStateFrontier.extend chain 2 base
def bad := CommonRoleCandidateStateFrontier.extend (seed .int) 0 .str

def parent : Declaration := ⟨0,0,[.tick (.var 0)],[(1,[.var 0]),(2,[.var 0])]⟩
def left : Declaration := ⟨1,1,[.var 0],[]⟩
def right : Declaration := ⟨2,2,[.int],[]⟩
def growing : Declaration := ⟨9,9,[.var 0],[(9,[.tick (.var 0)])]⟩
def goal : Goal := ⟨0,[(.tick (.var 0),.tick (.var 0))]⟩
def counts (registry : List Declaration) (s : State 3) :=
  (run registry slots sources goal s).map fun r => (r.snapshots.length,r.rebuilds,r.visits)

#guard (batches (State.empty : State 0)).length = 0
#guard CommonRoleCheckedOrdinaryReplay.validate (State.empty : State 0) (batches State.empty)
#guard (batches empty).length = 0
#guard (batches chain).length = 0
#guard CommonRoleOrdinaryKnownness.detect (seed .int).atoms 0 = none
#guard (batches (seed .int)).length = 3
#guard (batches (seed .str)).length = 3
#guard (batches (seed .bool)).length = 3
#guard (batches (seed .unit)).length = 3
#guard CommonRoleOrdinaryKnownness.detect (completed (seed .int)).atoms 0 = some .int
#guard CommonRoleOrdinaryKnownness.detect (completed (seed .str)).atoms 0 = some .str
#guard CommonRoleOrdinaryKnownness.detect (completed (seed .bool)).atoms 1 = some .bool
#guard CommonRoleOrdinaryKnownness.detect (completed (seed .unit)).atoms 2 = some .unit
#guard (batches bad).length = 6
#guard !CommonRoleCheckedOrdinaryReplay.validate bad (batches bad)
#guard counts [parent,left,right] empty = some (1,1,3)
#guard counts [parent,left,right] chain = some (1,1,3)
#guard counts [parent,left,right] (seed .int) = some (4,2,6)
#guard counts [parent,left,right] (seed .str) = some (4,1,3)
#guard counts [parent,left,right] (seed .bool) = some (4,1,3)
#guard counts [parent,left,right] bad = none
#guard counts [parent,left,right,growing] (seed .int) = none
#guard counts [parent,parent,left,right] (seed .int) = some (4,2,10)
#guard (batches (completed (seed .int))).length = 3
#guard (completed (completed (seed .int))).atoms.length > (completed (seed .int)).atoms.length

def singleEdge : State 3 :=
  ⟨[.tyLe (.var 0) (.var 2)],
    (by intro atom member; simp only [List.mem_singleton] at member; subst atom; trivial),
    (by intro source target member tail needed; simp only [List.mem_singleton] at member; cases member; cases needed),
    (by intro atom member; simp only [List.mem_singleton] at member; subst atom; trivial)⟩
def oneWay := CommonRoleCandidateStateFrontier.extend singleEdge 2 .int
#guard (batches oneWay).length = 1
#guard CommonRoleOrdinaryKnownness.detect (completed oneWay).atoms 0 = none

def rowBatch : State 3 :=
  ⟨[.rowLe (.var 0) (.var 1)],
    (by intro atom member; simp only [List.mem_singleton] at member; subst atom; trivial),
    (by intro source target member; simp at member),
    (by intro atom member; simp only [List.mem_singleton] at member; subst atom; rfl)⟩
def withRow := CommonRoleCheckedOrdinaryReplay.append (seed .int) rowBatch
#guard (batches withRow).length = 3
#guard CommonRoleCheckedOrdinaryReplay.validate withRow (batches withRow)

def emptyDecl : Declaration := ⟨1,1,[],[]⟩
def changingOld (i : Nat) : Plan (Fin 3) :=
  if i = 1 then [(99,(.base .int,.base .str))] else []
#guard (runGraphs [emptyDecl] slots sources ⟨1,[]⟩ (seed .int) changingOld).map
  (fun out => (out.1.rebuilds,out.2.map (fun pair => pair.2.map (fun graph => graph.edges.length)))) =
    some (1,[[6],[9],[10],[12]])
#guard (runGraphs [emptyDecl] slots sources ⟨1,[]⟩ bad changingOld).isNone
#guard (runGraphs [emptyDecl] slots sources ⟨1,[]⟩ withRow (fun _ => [])).map
  (fun out => out.2.map (fun pair => pair.2.map (fun graph => graph.rows.length))) =
    some [[1],[1],[1],[1]]

-- The initial parent has no complete plan; evidence later creates one.
-- Row preservation above is checked with a complete zero-child declaration.
#guard (runGraphs [parent,left,right] slots sources goal withRow (fun _ => [])).map
  (fun out => out.2.map (fun pair => pair.2.length)) = some [0,1,1,1]

example (s : State 3) (a : Fin 3 → Comp Common.model) :
    All Common.model a (completed s).atoms ↔ All Common.model a s.atoms := completed_models s a
example (s : State 3) (f : CommonRoleEvidenceSaturation.Fact 3) :
    f ∈ CommonRoleEvidenceSaturation.saturate (completed s) ↔
      f ∈ CommonRoleEvidenceSaturation.saturate s := completed_fixedpoint s f
example (s : State 3) (i : Fin 3) (b : Inference.Base) :
    CommonRoleOrdinaryKnownness.Evidence (completed s).atoms i b ↔
      CommonRoleEvidenceSaturation.Derived s (i,b) := completed_evidence s i b
example (s : State 3) (registry : List Declaration) :
    run registry slots sources goal s = none ↔
      ¬ s.Models ∨ ¬ CommonRoleIntervalWorkClosure.Checked registry := run_none_iff ..
end Cycle99BoundaryCheck
```

## Exact-source CI と最終公開準備

source 819bb1e77a8c3539ffae36636a4057f4cc68c2f4 の両CIは
2026-11-10T21:40:23Zまでの確認でcompleted/success。
- Core CI: https://github.com/momota1029/yulang/actions/runs/42907015599
- Lean inference kernel: https://github.com/momota1029/yulang/actions/runs/42907015621

source公開後のproduction Lean変更なし。ローカルsource treeと公開treeは完全一致。
最終公開はreportとcompleted heartbeatだけ。最終notes-only commitでLean CIが
再実行されなくても、上記exact-sourceの結果とLean blob不変を区別して報告する。
最終report準備: 2026-11-10T21:40:40Z。所要約12.2分（最終公開・照合時間は別）。
