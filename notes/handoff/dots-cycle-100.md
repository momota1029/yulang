# dots cycle 100 — 関連型とordinary evidenceの交互閉包

## 結果と部分目標

**関連型宣言から生まれるscalar等式と、ordinaryの相互変数辺による伝播を、
一つの有限Horn系で閉じた。associated→ordinary→associatedの交互依存を、
片方ずつ一回だけ実行する近似ではなく、独立な宣言導出とのiffまで証明した。**

部分目標は閉じた。`CommonRoleMixedEvidenceClosure`（225行）と
`CommonRoleMixedEvidenceReplay`（136行）、計19公開定理。
実ordinary solverとcached診断replayへ接続し、生成batchとtraceは内部で計算する。
source commit `3708055d9ebb87c5dfbc9ccf87fe35e8c2d8063c`、tree
`9a2d7563593f2cdc26296931323b6e8ed987363b`。公開10pathのblob一致と、
ローカルsource commit `d3a742629` との木全体一致を取得したremote treeで確認した。

4slotの回帰では、slot0のstrを関連型宣言がslot1へ流し、ordinary辺がslot2へ流し、
別の関連型宣言がslot3へ流す。旧associated→ordinary一回でも、旧ordinary→associated
一回でもslot3は未知のまま。今回のmixed閉包では4slotすべてstrになる。
この例は、任意のn、Source n、State nの一般定理の特殊例であり、単独の成果ではない。

T1c全体、外側resolve_exact、X13〜X16の外側入口、B4の5橋は未完成。
finite Source n、slot、identity、receiver templateは入力のまま。

## 定理の主張・量化・前提

以下のCは`Yulang.CommonRoleMixedEvidenceClosure`、Rは
`Yulang.CommonRoleMixedEvidenceReplay`。wfはcore WellFormed、awfは
AssocWellFormed。実行はwfを受け取るが、awfは独立な意味との対応の定理だけの前提。
State nは既存のchild/width/row grammar証明を持つ。

Cの11定理:

1. `saturate_exact`: 任意env/roles/wf/awf/Source n/State n/factについて、実cache所属 iff 独立なmixed Derives。Derivesは初期scalar pair、同じidentity、相互ordinary辺、独立なDeclarativeComputedによる関連型出力の4構成子。局所健全性・完全性。
2. `saturate_bounded`: 任意env/roles/wf/source/stateについて、実生成fact数は4*n以下。awfや充足可能性は不要。補助・有限進捗。
3. `saturate_nodup`: 同じ任意入力でfact列は重複なし。補助。
4. `saturate_stopped`: 同じ任意入力で、最終cacheにfresh enabled factは残らない。対象はこの有限混合規則系。補助・閉包。
5. `completed_models`: 任意env/roles/wf/awf/source/state/assignmentで、実出力の全atomを満たす iff 元stateを満たし、すべてのmixed導出factのscalar等式を満たす。関連型等式は元モデルを減らし得る。局所健全性・完全性。
6. `completed_evidence`: 任意同入力とslot/baseで、実出力に両向きscalar pairがある iff mixed Derives。矛盾stateにも成り立つ。局所健全性・完全性。
7. `completed_linked`: 任意env/roles/wf/source/state/2slotで、実出力の相互変数辺 iff 元stateの相互変数辺。scalar pair追加は新しい変数辺を作らない。補助。
8. `completed_derived`: 任意env/roles/wf/awf/source/state/factで、実出力からのmixed導出 iff 元stateからのmixed導出。局所健全性・完全性。
9. `completed_fixedpoint`: 同じ任意入力で、実出力を再飽和したcache所属 iff 元stateを飽和した所属。atom列のidempotenceではない。補助・閉包。
10. `derives_order_independent`: 任意env/roles/2source/state/factについて、source identityの等値関係とoccurrence所属が一致するなら両sourceのmixed導出は同値。wf/awf不要。順序・重複は結論に影響しない。補助。
11. `completed_models_order_independent`: 10と同じsource同値、およびwf/awfのもとで、任意assignmentについて実出力モデル集合が等しい。辞書やtraceの列同一性ではない。局所健全性・完全性。

Rの8定理:

12. `final_eq_completed`: 任意env/roles/wf/source/stateで、内部生成batchの実final stateはC.completedと文字どおり等しい。atom順序・重複を含む。補助。
13. `completed_models_iff`: 任意env/roles/wf/awf/source/stateで、実出力にモデルが存在 iff 元stateとすべての独立mixed導出を満たす共通assignmentが存在。局所健全性・完全性。
14. `validate_exact`: 同じ任意入力で、実ordinary solverが全生成traceを受理 iff 13の共通assignmentが存在。元stateの整合性だけでは十分でない。局所健全性・完全性。
15. `run_exact`: さらに任意diagnostic registry/slots/Sources/original Goal/outputについて、実runがoutputを返す iff 13のモデルが存在し、registryのChecked証明が存在し、outputは内部生成traceの実replayそのもの。role解決成功は前提にも結論にもない。局所健全性・完全性。
16. `run_none_iff`: 同じ任意入力で、none iff 13のモデルが無い、またはregistryがCheckedでない。局所健全性・完全性。
17. `batches_bounded`: 任意env/roles/wf/source/stateで内部生成batch数は4*n以下。補助。
18. `run_computed_bound`: 任意成功runについて、実workDomainの計算結果boundが存在し、snapshot数=1+実mixed fact数≤1+4*n、rebuild数≤1+元Goalの変数出現数、visit数≤その数×bound長。awfは不要。補助・有限進捗。
19. `run_graphs_exact`: 任意成功runと時点別old demandについて、graph付きrunも成功し、全graph出力は各実生成ordinary状態で既存public materialized runを直接呼んだ結果と一致。補助・出力一致。

局所健全性・完全性はこの明示した有限scalar/associated断片の対応。
M1全言語のTyping/infer・主型性の三つ組を完成させたわけではない。

## 保持した境界

- source graphはcaller入力。実parser、binder/source/invocation、動的where child、fresh slotを導いていない。既存の未回答identity質問を解決扱いにしない。
- Source.identityは既存のscalar fact伝播規則。seedが無いclassに任意の型の共有等式を加える意味は、この入口だけには無い。共通source全体の意味保存は別の橋。
- ordinary辺は元stateの明示的な相互辺。一方向の辺や一般のordinary entailmentの完全性は主張しない。新しい変数辺・未知のslotを生成しない。
- occurrence templateは有限な4baseに対して既存のassocOfでコンパイルする。ground化できないreceiverは出力を作らず保留。関連型scalar decoderは既存のint/str断片で、ordinary universeは4baseを保持する。
- generated factの順にbatchを作るが、Horn発見の時系列とは主張しない。実solverが全累積状態を検査する。二回目はfact不変でもatomを重ねて追加し得る。
- 元stateが充足可能でも関連型出力が矛盾を作ればrunはnone。回帰で、元stateはconsistent、完成後はinconsistentの例を検査した。
- diagnostic materializationは既存paired-int Form断片。str/bool/unitの言語仕様を変更していない。graphの充足可能性はordinary整合性から結論しない。
- visitは再構築treeのpreorder出現数。総runtime、solver内部仕事、graph構築の上限ではない。
- sole candidateを理由とするhead等式のcommitは追加しない。意味論の新規選択0件、質問ノート0件。

## 検証

最終production sourceに対し、以下はすべてexit 0。
指示どおり、全体のlocal lake build、全Audit、全AxiomGate、全verify-leanは未実行。
focused以外をローカル全体PASSとは呼ばない。

```text
cd lean; ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleMixedEvidenceReplay --wfail
✔ [350/351] Built Yulang.CommonRoleMixedEvidenceClosure (1.1s)
✔ [351/351] Built Yulang.CommonRoleMixedEvidenceReplay (1.1s)
Build completed successfully (351 jobs).
exit 0
```

```text
cd lean; ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang100/boundary-check.lean
exit 0
```

```text
cd lean; ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang100/axioms.lean
'Yulang.CommonRoleMixedEvidenceClosure.saturate_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleMixedEvidenceClosure.saturate_bounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleMixedEvidenceClosure.saturate_nodup' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMixedEvidenceClosure.saturate_stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleMixedEvidenceClosure.completed_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleMixedEvidenceClosure.completed_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleMixedEvidenceClosure.completed_linked' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMixedEvidenceClosure.completed_derived' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleMixedEvidenceClosure.completed_fixedpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleMixedEvidenceClosure.derives_order_independent' depends on axioms: [propext]
'Yulang.CommonRoleMixedEvidenceClosure.completed_models_order_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleMixedEvidenceReplay.final_eq_completed' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMixedEvidenceReplay.completed_models_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleMixedEvidenceReplay.validate_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleMixedEvidenceReplay.run_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleMixedEvidenceReplay.run_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleMixedEvidenceReplay.batches_bounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleMixedEvidenceReplay.run_computed_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleMixedEvidenceReplay.run_graphs_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

```text
python3 tools/boundary-input-inventory.py --check
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=268; Main=93; Audit=268; ledger mentioned=141. Mention counts are not audit completion counts.
exit 0
```

```text
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: . @ d3a742629 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
exit 0
```

34実行guardと2つの一般kernel example。交互依存、両一回順序の不足、任意cycleの
代表、seed無しcycle、occurrence重複・逆順、矛盾seed、関連型追加で初めて生じる
矛盾、未知receiverの保留、非相互の辺、slot0、row保持、invalid registry、二度目の
追加を検査した。19定理の公理はpropext / Classical.choice / Quot.soundのみ。
独立read-only reviewはblocking issueなし。reviewer自身はbuild/auditを実行していない。
最終module SHA256は以下で、reviewと一致:
- Closure: 14c78e155a2f54ba3961969ad66e656c4a80d2326f0cb9c2ba860a7a6c7746f0
- Replay: 876e896a4ce9c991f81b5da1ed46dc7a951cc239ffca5675792d8bee1fde8b82

git diff --check / git diff --cached --checkもexit 0。
最初のbuildは証明内のmember名の衝突で1箇所失敗し、局所名を分けて修正した。
最初のinventoryは未対応の--write指定で失敗し、既存の引数なし生成→--checkで修正。
commit前のdiff gateは未commit/untrackedのためFAILで、commit後にPASS。
背景shellの即時終了ではbuildが始まらない場合があり、timeout付きの非同期exec sessionへ
切り替えた。実行中の長時間前景待機、全体build、cacheコピーはしていない。
大きなファイルを一度に内部読取した際に出力上限でJSONが切れたため、60,000字ごとの
読取に切り替えた。公開内容は全blob SHAで照合した。未確認の書き込みの再試行なし。

## 仕様・実機・再開

spec6.3の関連型等式、兄弟安定までの遅延、兄弟の順序独立を再読した。
work/dots-auditをfetchしnotes/audit/x-oracle.mdのX13〜X16を再読。
shared-box、深さ2、同頭の局所区間、異頭の近似という既存観測であり、今回の
任意mixed source graphの実機証明ではない。新しいYulang2実行なし。

開始は2026-11-10T21:57:01Z。date記録21:57:29Z。integration/workは01cf4767。
最新standing orders/inboxはACTIVE、上限なし、I-11の25分、全体検証禁止を確認。
cycle99はcompletedとreportあり。保持workspaceへintegrationをmergeし、前cycleの
Lean/Lake/Git processと他のYulang writerが無いことを確認。復旧不要。
開始heartbeatは2f6830f2。最初のupdated値は手入力で実際の公開時刻より約32秒先に
なっていたため、その時刻は実公開時刻の証拠に使わない。次のheartbeatからdate由来の
UTCを使用。source heartbeat準備22:06:37Z、source公開・照合は22:09前。
10分境界のheartbeatはsourceと同時に公開され、目安より約1分遅れた。
20分前の途中source公開は達成。個別blob→SHAのみtree→commit→非force expected-head。
書き込みはwork/dots-mainだけ。integrationは読取・local mergeだけ。

source公開は9成果物とheartbeatの10path。最終report+completed heartbeatで異なる
pathは合計11。最終ref/tree/blob確認を終えてから親へ完了を報告する。
開始時・source公開後とも空き47G。clone追加、cacheコピー、データ削除なし。
使用量の枠は不明。ログは../cache/yulang100。

## B4の残り5橋と次候補

1. source_boundary_adequate: 実parser/declからscope、annotation、source/invocation、grammar-validな元stateを導く。
2. generated_work_closed: 今回の有限Source nを実where/associated生成とfresh-slot allocatorへ接続する。
3. saturate_terminates_and_closes: 一般に新しいrole/ordinary仕事・変数辺を生成するschedulerの進捗とfairness。今回のmixed有限閉包だけでは閉じない。
4. saturated_frontier_exact: 実飽和後と独立した最終4分類の接続。
5. resolve_dictionary_order_sound: 正準source義務順のdictionary観察同値。

次の候補は、(a) checked structural source programから今回のmixed Sourceを組み立てる
入口、(b) 既存source tableの共有等式を組み込んだ全source valuationとの対応、
(c) 実新規変数辺・childの有限生成域。今回は関連型とordinary scalarが交互に新事実を
作る固定の有限領域を閉じたが、B4の主定理には依然5橋が要る。

## 再実行可能な境界回帰

```lean
import Yulang.CommonRoleMixedEvidenceReplay
open Yulang
open CommonRoleSettledConstraints (State)
open CommonRoleFiniteAssociatedClosure (Source Occurrence)
open CommonRoleCandidateStateFrontier (extend)
open CommonRoleStablePaterson (Declaration)
open CommonRoleGuardedIntervalPlans (Sources Plan)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All Atom)
namespace Cycle100
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 2048
open Roles.AssocExamples

def atoms : List (Atom (Fin 4)) := [.tyLe (.var 1) (.var 2), .tyLe (.var 2) (.var 1)]
def edges : State 4 where
  atoms := atoms
  child := by intro a h; simp only [atoms,List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl | rfl <;> trivial
  width := by intro a b h tail ht; simp only [atoms,List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with h | h <;> cases h <;> cases ht
  rows := by intro a h; simp only [atoms,List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl | rfl <;> trivial

def template (b : Inference.Base) : Roles.Goal :=
  index (box ((CommonRoleOrdinaryKnownness.encode b).getD Roles.Examples.int)) Roles.Examples.int

def first : Occurrence 4 := ⟨0,1,0,template⟩
def second : Occurrence 4 := ⟨2,3,0,template⟩
def source : Source 4 := ⟨Fin.val,[first,second]⟩
def reverse : Source 4 := ⟨Fin.val,[second,first]⟩
def duplicate : Source 4 := ⟨Fin.val,[first,second,first]⟩
def cycle : Source 4 := ⟨Fin.val,[first,second,⟨3,0,0,template⟩]⟩
def initial := extend edges 0 .str

def cache (p : Source 4) (s : State 4) :=
  CommonRoleMixedEvidenceClosure.saturate (singletonEnv boxImpl) requiredRoles box_paterson p s
def finish (p : Source 4) (s : State 4) :=
  CommonRoleMixedEvidenceClosure.completed (singletonEnv boxImpl) requiredRoles box_paterson p s

def oldAssoc (s : State 4) :=
  CommonRoleFiniteAssociatedModels.run (singletonEnv boxImpl) requiredRoles box_paterson source s

-- Neither fixed one-pass ordering closes this alternating chain.
#guard (CommonRoleEvidenceSaturation.saturate initial).length = 1
#guard (CommonRoleFiniteAssociatedClosure.saturate (singletonEnv boxImpl) requiredRoles box_paterson source initial).length = 2
#guard CommonRoleOrdinaryKnownness.detect (CommonRoleEvidenceReplay.completed (oldAssoc initial)).atoms 3 = none
#guard CommonRoleOrdinaryKnownness.detect (oldAssoc (CommonRoleEvidenceReplay.completed initial)).atoms 3 = none
#guard (cache source initial).length = 4
#guard CommonRoleOrdinaryKnownness.detect (finish source initial).atoms 0 = some .str
#guard CommonRoleOrdinaryKnownness.detect (finish source initial).atoms 1 = some .str
#guard CommonRoleOrdinaryKnownness.detect (finish source initial).atoms 2 = some .str
#guard CommonRoleOrdinaryKnownness.detect (finish source initial).atoms 3 = some .str
#guard (cache reverse initial).length = 4
#guard (cache duplicate initial).length = 4
#guard (cache cycle initial).length = 4
#guard (cache source edges).length = 0
#guard (cache cycle edges).length = 0
#guard (cache source (finish source initial)).length = 4
#guard (finish source (finish source initial)).atoms.length > (finish source initial).atoms.length
#guard CommonRoleOpenPropagation.consistent (finish source initial)
#guard !CommonRoleOpenPropagation.consistent (finish source (extend initial 3 .int))

-- Associated equations can make an initially consistent state inconsistent.
#guard CommonRoleOpenPropagation.consistent (extend initial 3 .int)

def slots : Nat → Fin 4 := fun n => ⟨n%4,Nat.mod_lt _ (by decide)⟩
def sources : Sources := fun _ _ binder => binder
def decl : Declaration := ⟨1,1,[],[]⟩
def growing : Declaration := ⟨9,9,[.var 0],[(9,[.tick (.var 0)])]⟩
def run (p : Source 4) (s : State 4) (registry : List Declaration) :=
  CommonRoleMixedEvidenceReplay.run (singletonEnv boxImpl) requiredRoles box_paterson p s registry slots sources ⟨1,[]⟩
#guard (run source initial [decl]).map (fun r => (r.snapshots.length,r.rebuilds,r.visits)) = some (5,1,1)
#guard (run source edges [decl]).map (fun r => r.snapshots.length) = some 1
#guard (run source (extend initial 3 .int) [decl]).isNone
#guard (run source initial [decl,growing]).isNone
#guard (run duplicate initial [decl]).map (fun r => r.snapshots.length) = some 5

-- Row constraints and per-occurrence old graph demands are retained.
def row : State 4 :=
  ⟨[.rowLe (.var 0) (.var 1)],
    (by intro a h; simp only [List.mem_singleton] at h; subst a; trivial),
    (by intro a b h; simp at h),
    (by intro a h; simp only [List.mem_singleton] at h; subst a; rfl)⟩
def withRow := CommonRoleCheckedOrdinaryReplay.append initial row
#guard (cache source withRow).length = 4
#guard (CommonRoleMixedEvidenceReplay.runGraphs (singletonEnv boxImpl) requiredRoles box_paterson source withRow [decl] slots sources ⟨1,[]⟩ (fun _ => [])).map (fun r => r.2.map (fun pair => pair.2.map (fun g => g.rows.length))) = some [[1],[1],[1],[1],[1]]

example (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Source n) (s : State n) (f : CommonRoleFiniteAssociatedClosure.Fact n) :
    f ∈ CommonRoleMixedEvidenceClosure.saturate env roles wf p s ↔
      CommonRoleMixedEvidenceClosure.Derives env roles p s f :=
  CommonRoleMixedEvidenceClosure.saturate_exact env roles wf awf p s f
example (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Source n) (s : State n) (f : CommonRoleFiniteAssociatedClosure.Fact n) :
    f ∈ CommonRoleMixedEvidenceClosure.saturate env roles wf p (CommonRoleMixedEvidenceClosure.completed env roles wf p s) ↔
      f ∈ CommonRoleMixedEvidenceClosure.saturate env roles wf p s :=
  CommonRoleMixedEvidenceClosure.completed_fixedpoint env roles wf awf p s f

-- Empty allocation, missing seed, unresolved receiver and non-reciprocal edge.
def noSource : Source 0 := ⟨fun i => Fin.elim0 i,[]⟩
#guard (CommonRoleMixedEvidenceClosure.saturate (singletonEnv boxImpl) requiredRoles box_paterson noSource State.empty).length = 0

def unknown : Source 4 := ⟨Fin.val,[⟨0,1,0,fun _ => index (.var 0) Roles.Examples.int⟩]⟩
#guard (cache unknown initial).length = 1
#guard CommonRoleOrdinaryKnownness.detect (finish unknown initial).atoms 1 = none
#guard (run unknown initial [decl]).isSome

def oneWay : State 4 :=
  ⟨[.tyLe (.var 1) (.var 2)],
    (by intro a h; simp only [List.mem_singleton] at h; subst a; trivial),
    (by intro a b h tail ht; simp only [List.mem_singleton] at h; cases h; cases ht),
    (by intro a h; simp only [List.mem_singleton] at h; subst a; trivial)⟩
#guard (cache source (extend oneWay 0 .str)).length = 2
#guard CommonRoleOrdinaryKnownness.detect (finish source (extend oneWay 0 .str)).atoms 3 = none
#guard !CommonRoleOpenPropagation.consistent (extend (extend edges 0 .int) 0 .str)
#guard (run source (extend (extend edges 0 .int) 0 .str) [decl]).isNone
end Cycle100
```

## Exact-source CI と最終公開

source 3708055d9ebb87c5dfbc9ccf87fe35e8c2d8063c の両CIは
2026-11-10T22:11:34Zまでの確認でcompleted/success。
- Core CI: https://github.com/momota1029/yulang/actions/runs/42911758723
- Lean inference kernel: https://github.com/momota1029/yulang/actions/runs/42911758460

source公開後にproduction Lean変更なし。最終公開はreportとcompleted heartbeatのみ。
最終notes-only commitでLean CIが再実行されなくても、上記exact-sourceの成功と
Lean blob不変を区別して報告する。
最終report準備: 2026-11-10T22:12:11.447441Z。所要約15.2分
（最終公開・照合時間は別）。部分目標を閉じ、不要な補題で残り時間を埋めない。
