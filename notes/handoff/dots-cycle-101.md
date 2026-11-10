# dots cycle 101 — 構造的ソースと物理的共有からmixed閉包へ

## 結果と部分目標

**検査済みの構造的な有限occurrence列から、slotとsource同一性を計算して、
関連型とordinaryの交互閉包へ接続した。実出力の全モデルが、独立な名前上の
導出と単一のsource型valuationに一致することを証明した。**

部分目標は閉じた。新規 `CommonRoleStructuralMixedSource` は222行、10公開定理。
cycle100の任意Source n入口を、既存のraw検査と構造的goal生成へつないだ。
sourceの物理的な等式も加えるので、scalar seedの無い同名occurrence同士も型を
共有する。effect成分は共有しない。

source commit `0ffd4dcc5ffca96717aea6edf6766af85b9aa1ca`、tree
`b03e1bd284c82cebe132ee12e97b39fed48ba502`。8成果物とheartbeatの9pathを公開し、
取得した全9blobがlocalと一致、さらにlocal source commit `624c325a8` と
取得したremoteの木全体のdiffが空であることを確認した。

例では、source10→20の関連型、20と30の元ordinary相互辺、30→40の関連型、
別occurrenceのsource40の共有、40→50の関連型を交互に解く。
旧associated-only入口ではsource50は未知のまま、新入口では全6slotがstrになる。
これは任意のprogram/stateを量化する一般定理の回帰例。
T1c全体・外側resolve_exact・X13〜X16の外側入口・B4の5橋は未完成。

## 一般定理の主張と前提

以下はすべて `Yulang.CommonRoleStructuralMixedSource`。
pは任意の有限structural Program、sは任意のState (table p).length。
Stateは既存のchild/width/row grammar証明を持つ。
wfはcore WellFormed、awfはAssocWellFormed。名前はscope解決済みの入力。

1. `prepared_linked`: 任意p/s/2slotについて、source等式を追加した後の相互辺 iff 元stateの相互辺、または2slotのsource名が等しい。補助。宣言well-formedness不要。
2. `allocated_to_named`: 任意env/roles/p/s/factについて、allocated mixed導出があれば、元source名上の独立Derivesがある。局所健全性。wf/awf不要。
3. `named_to_allocated`: 任意env/roles/p/s/name/baseの独立Derivesについて、そのnameを持つすべてのslotにallocated mixed導出がある。局所完全性。wf/awf不要。
4. `allocated_named_exact`: 同じ任意入力について2と3のiff。局所健全性・完全性。
5. `named_support`: 任意の独立Derivesのnameは、実計算tableのslotに現れる。空programやcycleにも成り立ち、未使用nameへ等式を課さない。補助。
6. `run_evidence_exact`: 任意env/roles/wf/awf/p/s/slot/baseについて、実出力atomに両向きscalar evidenceがある iff そのsource名に独立Derivesがある。局所健全性・完全性。
7. `run_source_exact`: 任意env/roles/wf/awf/p/s/assignment vについて、vが実出力の全atomを満たす iff 元sを満たし、vの型成分を全occurrenceで因数分解する単一のsource valuationが存在し、そのvaluationが全独立Derivesのscalar等式を満たす。局所健全性・完全性。モデル存在やsource coherenceは前提ではない。
8. `solver_source_exact`: 任意env/roles/wf/awf/p/sについて、実ordinary solverが受理 iff 7の共通assignmentとsource valuationが存在する。局所健全性・完全性。成功・fuel・外部boundを前提にしない。
9. `capacity`: 任意env/roles/wf/p/sについて、mixed飽和の異なるscalar fact数は8*p.length以下。awfや整合性不要。補助・有限進捗。2slot/occurrenceと4baseから計算する。
10. `checked_source_exact`: さらに任意raw programと、既存checkがpを返す結果について、pのeraseはrawそのもので、rawはscope/arity/関連型名検査を満たし、7のiffが成立。チェック成功は整合性や解決成功を保証しない。局所健全性・完全性。

独立Derivesは、元stateの明示的scalar seed、元stateの相互変数辺、構造的
Materializesと独立role/associated宣言導出からなる。実resolver・saturate・
生成済みfrontierはそのjudgmentに含めない。上記はM1全言語のTyping/inferの
健全性・完全性・主型性の三つ組を完成させるものではない。

## 境界と受け入れ条件

- 構造的template、computed slot/source identity、物理的共有、mixed閉包の局所接続は達成。
- 元sのslotは選ばれたoccurrenceの二つの位置に限る。ordinary専用変数を別のslotに置く一般のallocationは未接続。
- scope解決済みの名前、finite occurrence選択、元grammar-valid state、role registryは依然入力。実parserからの意味保存ではない。
- 一方向のordinary辺や一般のsemantic entailmentを完全に検出するものではない。aliasの別slotに分かれたlower/upperから、実solverは矛盾を見つけても、明示的scalar seedが無ければこのcacheは空になり得る。
- bool/unitはordinaryのfact universeにあるが、既存のassociated structural adapterはint/str。未対応headで勝手に意味を足さない。
- computed tableを並べ替えた場合のslot reindexingによる一般同値は未証明。cycle100の同じslot universe上の順序独立を、そのままこの新入口の全順序独立と呼ばない。
- 実新規where child、fresh slot、invocation identity、一般schedulerのfairness、最終四分類、辞書の観察同値は未達。
- 新規意味論の選択0件、質問ノート0件。既存のidentity質問は未回答のまま。
- spec6.3の関連型等式、兄弟の安定待ちと順序独立を再読。新しいYulang2実行なし。

## 検証

最終production sourceで以下はすべてexit 0。
指示どおり、全体local lake build、全Audit、全AxiomGate、全verify-leanは未実行。
focusedとdiff-onlyを全体PASSとは呼ばない。

```text
cd lean; ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleStructuralMixedSource --wfail
✔ [357/357] Built Yulang.CommonRoleStructuralMixedSource (5.3s)
Build completed successfully (357 jobs).
exit 0
```

```text
cd lean; ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang101/boundary-check.lean
exit 0
```

```text
cd lean; ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang101/axioms.lean
'Yulang.CommonRoleStructuralMixedSource.prepared_linked' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMixedSource.allocated_to_named' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMixedSource.named_to_allocated' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMixedSource.allocated_named_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMixedSource.named_support' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStructuralMixedSource.run_evidence_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralMixedSource.run_source_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralMixedSource.solver_source_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralMixedSource.capacity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStructuralMixedSource.checked_source_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

```text
python3 tools/boundary-input-inventory.py --check
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=269; Main=93; Audit=269; ledger mentioned=142. Mention counts are not audit completion counts.
exit 0
```

```text
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: . @ 2ccd78b85 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
exit 0
```

32 executable guards、3 kernel examplesとno_seed補題を検査した。
交互のassociated/ordinary/identity伝播、seed無し閉路、関連型が初めて作る矛盾、
seed無し同名classのsplit bounds矛盾、一方向辺の非伝播、未対応headの保留、
scope/arity/関連型名の不正入力、空program、重複、self-useを含む。
同じsourceの型が一致しつつ、effect成分は異なってよい具体的なmodelもkernelで確認。
10定理の公理はpropext / Classical.choice / Quot.soundのみ。
独立read-only reviewはblocking issueなし。reviewer自身はbuild/auditを実行していない。
production module SHA256:
`e69a8ad075244d984351dcf25df968f9a8235e77f052d5c7df7cf8d1d6a09aba`。

初回focused buildは定義展開・dependent rewriteの局所箇所で失敗し修正した。
回帰の初回はFinのNeZero instance、型constructor名、既存wellFormed補題名を直した。
最後のfocusedと回帰はwarning無しで成功。期待値の変更による合わせ込みはしていない。
git diff --check / git diff --cached --checkも成功。

## 復旧・公開・運用

開始2026-11-10T22:29:19Z。最新integration/workはe79efbdc。
最新standing orders/inboxのACTIVE、上限なし、I-11の25分、全体検証禁止を確認。
cycle100はcompletedでreportあり。保持workspaceでintegrationをmergeし、
前cycleのLean/Lake/Git processと他のwriterが無いことを確認。復旧不要。
最初のfetchではworkのremote-trackingが古かったため、明示refspecで更新し、
APIのlive refと照合した。統合ブランチへの書込みはしていない。

開始heartbeatは3f877dc8。最初のupdatedは手入力で実公開より約34秒先だったため、
実公開時刻の証拠には使わない。以後はdate/Python UTC由来。
source公開は22:39:18Z、開始10分より前。source heartbeatは準備時刻22:36:35Z。
10分のheartbeatは22:39台に更新して公開3c07aa82、遅れは1分未満。
個別blobを作り、SHAのみtreeでlive treeを保持し、非force expected-headで公開。
9blobと取得した木全体を照合。拒否・承認待ち・未確定書込みの再試行なし。

成果物8path、heartbeat、最終reportで異なるpathは合計10。
開始時の空き47G。clone増設、cacheコピー、データ削除なし。
使用量の枠は不明。ログは../cache/yulang101。

## B4の残り5橋と次候補

1. source_boundary_adequate: 実parser/declからscope・annotation・source/invocation・元stateを導く。
2. generated_work_closed: finite occurrenceの実where/関連型生成とordinary専用変数を含むfresh allocatorへの接続。
3. saturate_terminates_and_closes: 新しい仕事・変数辺・slotを生成する一般schedulerの進捗とfairness。
4. saturated_frontier_exact: 実飽和後と独立した最終4分類の接続。
5. resolve_dictionary_order_sound: 正準source義務順のdictionary観察同値。

次の候補: (a) finite structural programのordinary専用変数を含むallocation、
(b) occurrence順序変更のtable reindexingとモデル集合の対応、
(c) checked sourceから実生成childまでの閉包。
今回の局所橋を閉じても、B4主定理には同じ5橋が残る。

## 再実行可能な境界回帰

```lean
import Yulang.CommonRoleStructuralMixedSource
open Yulang
open CommonRoleSettledConstraints (State)
open CommonRoleCandidateStateFrontier (extend)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All Atom)
open Roles.AssocExamples
namespace Cycle101
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 2048
open CommonRoleStructuralAssociatedTemplates (Program Occurrence table compile)
open CommonRoleStructuralMixedSource (run)

def template : CommonRoleStructuralAssociatedTemplates.Template :=
  ⟨index (box (.var 0)) Roles.Examples.int,by decide⟩
def p : Program := [⟨10,20,0,template⟩,⟨30,40,0,template⟩,⟨40,50,0,template⟩]
instance : NeZero (table p).length := ⟨by decide⟩
def raw := CommonRoleCheckedAssociatedPrograms.eraseProgram p
#guard (CommonRoleCheckedAssociatedPrograms.check requiredRoles raw).isSome
#guard table p = [10,20,30,40,40,50]

def atoms : List (Atom (Fin (table p).length)) := [.tyLe (.var 1) (.var 2),.tyLe (.var 2) (.var 1)]
def edges : State (table p).length where
  atoms := atoms
  child := by intro a h; simp only [atoms,List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl | rfl <;> trivial
  width := by intro a b h tail ht; simp only [atoms,List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with h | h <;> cases h <;> cases ht
  rows := by intro a h; simp only [atoms,List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl | rfl <;> trivial

def initial := extend edges 0 .str
def finish (s : State (table p).length) := run (singletonEnv boxImpl) requiredRoles box_paterson p s
def cache (s : State (table p).length) :=
  CommonRoleMixedEvidenceClosure.saturate (singletonEnv boxImpl) requiredRoles box_paterson
    (CommonRoleNamedAssociatedSourceModels.source (compile p))
    (CommonRoleNamedAssociatedSourceModels.prepared (compile p) s)
#guard (cache initial).length = 6
#guard CommonRoleOrdinaryKnownness.detect (finish initial).atoms 0 = some .str
#guard CommonRoleOrdinaryKnownness.detect (finish initial).atoms 1 = some .str
#guard CommonRoleOrdinaryKnownness.detect (finish initial).atoms 2 = some .str
#guard CommonRoleOrdinaryKnownness.detect (finish initial).atoms 3 = some .str
#guard CommonRoleOrdinaryKnownness.detect (finish initial).atoms 4 = some .str
#guard CommonRoleOrdinaryKnownness.detect (finish initial).atoms 5 = some .str
#guard CommonRoleOrdinaryKnownness.detect
  (CommonRoleStructuralAssociatedTemplates.run (singletonEnv boxImpl) requiredRoles box_paterson p initial).atoms 5 = none
#guard CommonRoleOpenPropagation.consistent (finish initial)
#guard (cache edges).length = 0
#guard CommonRoleOpenPropagation.consistent (finish edges)
#guard (cache (finish initial)).length = 6
#guard !CommonRoleOpenPropagation.consistent (finish (extend initial 5 .int))
#guard CommonRoleOpenPropagation.consistent (extend initial 5 .int)

-- A seedless shared class still has physical type equality constraints.
def shared : Program := [⟨10,20,0,template⟩,⟨10,30,0,template⟩]
instance : NeZero (table shared).length := ⟨by decide⟩
def bounds : List (Atom (Fin (table shared).length)) :=
  [.tyLe (.base .int) (.var 0),.tyLe (.var 2) (.base .str)]
def unseeded : State (table shared).length where
  atoms := bounds
  child := by intro a h; simp only [bounds,List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl | rfl <;> trivial
  width := by intro a b h tail ht; simp only [bounds,List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with h | h <;> cases h <;> cases ht
  rows := by intro a h; simp only [bounds,List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl | rfl <;> trivial
#guard CommonRoleOpenPropagation.consistent unseeded
#guard !CommonRoleOpenPropagation.consistent (run (singletonEnv boxImpl) requiredRoles box_paterson shared unseeded)
#guard (CommonRoleMixedEvidenceClosure.saturate (singletonEnv boxImpl) requiredRoles box_paterson
  (CommonRoleNamedAssociatedSourceModels.source (compile shared))
  (CommonRoleNamedAssociatedSourceModels.prepared (compile shared) unseeded)).length = 0

-- A directed edge alone is not treated as reciprocal scalar evidence.
def oneWay : State (table p).length :=
  ⟨[.tyLe (.var 1) (.var 2)],
   (by intro a h; simp only [List.mem_singleton] at h; subst a; trivial),
   (by intro a b h tail ht; simp only [List.mem_singleton] at h; cases h; cases ht),
   (by intro a h; simp only [List.mem_singleton] at h; subst a; trivial)⟩
#guard (cache (extend oneWay 0 .str)).length = 2
#guard CommonRoleOrdinaryKnownness.detect (finish (extend oneWay 0 .str)).atoms 5 = none
#guard (cache (extend edges 0 .bool)).length = 1
#guard CommonRoleOrdinaryKnownness.detect (finish (extend edges 0 .bool)).atoms 1 = none

-- Scope/arity/name checks are independent of the ordinary solver.
def badScope : CommonRoleCheckedAssociatedPrograms.RawProgram := [⟨10,20,0,index (box (.var 1)) Roles.Examples.int⟩]
def badArity : CommonRoleCheckedAssociatedPrograms.RawProgram := [⟨10,20,0,⟨template.goal.role,[]⟩⟩]
def badName : CommonRoleCheckedAssociatedPrograms.RawProgram := [⟨10,20,99,template.goal⟩]
#guard (CommonRoleCheckedAssociatedPrograms.check requiredRoles badScope).isNone
#guard (CommonRoleCheckedAssociatedPrograms.check requiredRoles badArity).isNone
#guard (CommonRoleCheckedAssociatedPrograms.check requiredRoles badName).isNone
#guard (CommonRoleCheckedAssociatedPrograms.check requiredRoles []).isSome
#guard (run (singletonEnv boxImpl) requiredRoles box_paterson [] State.empty).atoms = []

example (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Program) (s : State (table p).length) (v : Fin (table p).length → Comp Common.model) :
    All Common.model v (run env roles wf p s).atoms ↔
      All Common.model v s.atoms ∧ ∃ values, CommonRoleSourceDescent.Factors (table p) v values ∧
        ∀ a b, CommonRoleStructuralMixedSource.Derives env roles p s a b →
          Common.Equivalent (values a) (.base b) :=
  CommonRoleStructuralMixedSource.run_source_exact env roles wf awf p s v

-- Cycles, duplication and self-use stay inside the finite source.
def cyc : Program := [⟨10,20,0,template⟩,⟨20,10,0,template⟩]
def dup : Program := [⟨10,20,0,template⟩,⟨10,20,0,template⟩]
def self : Program := [⟨10,10,0,template⟩]
instance : NeZero (table cyc).length := ⟨by decide⟩
instance : NeZero (table dup).length := ⟨by decide⟩
instance : NeZero (table self).length := ⟨by decide⟩
#guard CommonRoleOrdinaryKnownness.detect (run (singletonEnv boxImpl) requiredRoles box_paterson cyc State.empty).atoms 0 = none
#guard CommonRoleOrdinaryKnownness.detect (run (singletonEnv boxImpl) requiredRoles box_paterson cyc (extend State.empty 0 .str)).atoms 3 = some .str
#guard CommonRoleOrdinaryKnownness.detect (run (singletonEnv boxImpl) requiredRoles box_paterson dup (extend State.empty 0 .str)).atoms 3 = some .str
#guard CommonRoleOrdinaryKnownness.detect (run (singletonEnv boxImpl) requiredRoles box_paterson self (extend State.empty 0 .str)).atoms 1 = some .str

theorem no_seed (p : Program) (a : Nat) (b : Inference.Base)
    (h : CommonRoleStructuralMixedSource.Derives (singletonEnv boxImpl) requiredRoles p State.empty a b) : False := by
  induction h with
  | initial seed =>
    obtain ⟨_,_,evidence⟩ := seed
    simp [CommonRoleOrdinaryKnownness.Evidence,State.empty] at evidence
  | transfer _ _ ih => exact ih
  | associated _ _ _ _ ih => exact ih

def differentRows (i : Fin (table shared).length) : Comp Common.model :=
  (.base .int, fun _ => i.val = 0)
example : All Common.model differentRows
    (run (singletonEnv boxImpl) requiredRoles box_paterson shared State.empty).atoms := by
  apply (CommonRoleStructuralMixedSource.run_source_exact (singletonEnv boxImpl) requiredRoles
    box_paterson box_assoc_wellFormed shared State.empty differentRows).mpr
  refine ⟨?_,fun _ => .base .int,?_,?_⟩
  · intro atom member; cases member
  · intro slot; exact Common.equivalent_refl _
  · intro a b derived; exact False.elim (no_seed shared a b derived)
example : (differentRows 0).2 ≠ (differentRows 2).2 := by
  intro equal
  have h := congrFun equal (0,[])
  simp [differentRows] at h
end Cycle101
```

## Exact-source CI と最終公開

source 0ffd4dcc5ffca96717aea6edf6766af85b9aa1ca の両CIは
2026-11-10T22:41:27Zの確認でcompleted/success。
- Core CI: https://github.com/momota1029/yulang/actions/runs/42916540545
- Lean inference kernel: https://github.com/momota1029/yulang/actions/runs/42916540445

source公開後にproduction Lean変更なし。最終公開はreportとcompleted heartbeatのみ。
最終notes-only commitのCIと、上記exact-source CIおよびLean blob不変を区別する。
read-only reviewerは最終production SHAを再確認し、追加回帰の期待値も妥当、blockerなし。
回帰commentから未実施のpermutationという語だけ除いた。並べ替え同値は未証明のまま。
終了時の空き47G。最終ref/tree/blobを取得して照合後、親へ完了を報告する。

最終report準備: 2026-11-10T22:41:56.012231Z、所要約12.6分（最終公開・照合は別）。
部分目標を閉じ、時間を埋めるだけの補題は追加しなかった。
