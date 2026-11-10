# dots cycle 76 — finite associated closureとordinary source同一性

## 結果

**有限associated graph断片の共有source model接続を閉じた。**
新規`CommonRoleFiniteAssociatedSourceModels`は、同名occurrenceのordinary型等式を
先に追加し、既存の有限associated飽和へ渡す。全assignmentについて、結果のmodelと
「元の制約・一つのsource valuation・独立associated宣言導出の全等式」が同値。
実ordinary solverの受理も、そのmodel存在と同値になった。

ソース公開: [`ce61b5dd6ab7663cb094d04ca1751b8b1797f9b5`](https://github.com/momota1029/yulang/commit/ce61b5dd6ab7663cb094d04ca1751b8b1797f9b5)。
公開tree `a11e706b2e1bc5756fb794074c813c97082a576d` は
local検証commit `9b92212ff0973ab963a8a44163b32daf8899ca1c` のtreeと完全一致する。

I-13の台帳M節は、Mainの有限path入口と関連型/有限graphの既存13モジュール、
新規1モジュールについて、caller入力・補助前提・仕様の根拠・source生成義務を対応づけた。
inventoryはCommonRole 243、Main到達93、Audit到達243、台帳言及116。
**言及数は全入力監査済み数ではない。I-13全体は部分達成で、cycle72期限超過は解消しない。**

## 何が不足していたか

既存finite graphのidentityRulesは、既知scalar factを同名slotへ伝播する。
未知の同名slotを一般ordinary型として等置する制約は、既存run自身では追加しない。
実際、同名二slotでseedもoccurrenceも無ければ、既存runのatomsは空であり、
slot0=int、slot1=strの分裂assignmentもmodelになる。
新入口がこのassignmentを排除することをLeanで確認した。

これは旧定理の誤りではない。旧定理が主張していた有限scalar閉包から、source同一性を
保つordinary modelへ接続する責任が残っていた。既存NamedPathでは同一性を先に
追加していたため、その接続の違いも台帳に明記した。

実行への入力は、任意の有限table、同じ長さのslotを参照するoccurrence列、
first-order env/roles、core well-formedness、任意の旧ordinary state。
独立宣言判断とのiffにはassociated well-formednessを明示する。
source valuationは結論で存在量化され、callerが選ぶ実行oracleではない。
型同一性だけを追加し、effect行の同一性を勝手に追加しない。

## 新規定理と量化範囲

全て`Yulang.CommonRoleFiniteAssociatedSourceModels`内。
1. `run_models_exact`（健全性・完全性）:
   任意のenv/roles、core/associated well-formedness、table、有限occurrence列、旧state、
   全occurrence assignmentに対し、返却stateのmodel iff 元stateのmodel、source coherence、
   独立associated導出から得られる全scalar等式。
2. `source_factorization`（健全性・補助）:
   任意のenv/roles/core well-formedness、table、occurrence列、旧state、返却modelについて、
   元stateのmodelが保持され、一つのsource型valuationへfactorする。
   この補助にはassociated well-formednessは不要。
3. `run_source_models_exact`（健全性・完全性）:
   1と同じ全量化と明示well-formednessの下で、返却model iff 元stateのmodelかつ、
   同じsource valuationへのfactorizationと全独立associated等式を満たすvaluationが存在。
4. `solver_source_exact`（健全性・完全性のsolver接続）:
   任意の同じenv/roles/well-formedness/table/occurrences/旧stateに対し、実ordinary solverの
   consistent=true iff 3の右辺を満たすassignmentとsource valuationが存在。

全言語の主型性や四方向分類は結論に含めない。有限graph、template関数、scopeを含む
source名の妥当性は入力のまま。この有限範囲は実装断片であり仕様による拒否範囲ではない。
既存定理の変更0、新しい言語意味の選択0、新規質問0。

## 検証

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build --wfail Yulang.CommonRoleNamedAssociatedGraph Yulang.CommonRoleNamedPath Yulang.CommonRoleAssociatedDeclarationExact
Build completed successfully (290 jobs).
exit 0

ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build --wfail Yulang.CommonRoleFiniteAssociatedSourceModels
Build completed successfully (284 jobs).
exit 0

ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang76/boundary-check.lean
exit 0
```

scratchは15境界assertion（14 exampleと1個の名前つき反証）を検査した。
新規4定理と既存5定理の公理出力はpropext / Classical.choice / Quot.soundのみ。
境界検査は最初、定義されたlist長に対するFin数値literalの型推論で失敗した。
明示したFin値とval列の比較へ直して同じ期待を再検査し、exit 0。production証明は変更せず通った。
最初の背景shell起動は子processを保持せず、また一度ログ相対pathを誤ったため実行前に失敗。
実行済みとは数えず、上記timeout付きsessionで実行し直した。長い全体buildは走らせていない。

`python tools/boundary-input-inventory.py --check`、`git diff --check`はexit 0。
M節で名指した14 moduleの全path存在も確認した。

`bash tools/verify-lean.sh . origin/integration/m1-final --no-build`の全文（exit 0）:

```text
verify-lean: . @ 9b92212ff (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

dotでは全体lake build、全Audit/AxiomGate、build付きverify-leanを実行していない。
公開source commit `ce61b5dd` のCIは両方success:
- [Core CI](https://github.com/momota1029/yulang/actions/runs/42792587790): 09:40:22 UTC終了。
- [Lean inference kernel](https://github.com/momota1029/yulang/actions/runs/42792587643):
  09:41:18 UTC終了。build、全宣言監査、例実行stepが全てsuccess。

## Yulang2との照合

live work/dots-audit `55574b6052ef1534fd0fc36d6d3617ebede59a0e`のx-oracleを取得した。
C3-PARENTのleft/right両順とgeneric-functionの(11,22)、missing-child拒否を参照。
X13〜X16の局所区間結果も参照したが、内部table/template/ordinary source同一性の
直接oracleではない。新しいYulang2実機実行やparser実行はしていない。
spec6.2/6.3のsource共有と関連型等式に従い、既存Q1/Q2、cycle23/24を維持する。

## 公開、復旧、資源

開始時にlive integration/workが両方eb200058であることを確認し、standing-ordersと
inboxを再読。I-11の25分上限と全体build禁止を適用した。
前回cycle75はcompletedで報告も存在し、復旧は不要だった。
一つの既存作業場を再利用。local-cycle33の履歴は残し、API統合版からlocal-cycle76を作った。

- 開始トリガー09:27:19 UTC。最初のdate記録は09:28:55。
- 開始心拍公開09:29:26、10分心拍公開09:37:19。
- 8pathのsource/doc公開09:39:47、開始から12.5分。20分時点より早く公開した。
- 8blobを準備し、全SHAをlocal内容と照合してから一つのtree/commitへまとめた。
  workのみをforce=false、expected_sha=c6eab9dff…で更新した。
- recursive tree全2284entryを再取得し、8path全blobとtree全体が一致。
  integrationはeb200058のまま。このcycleでwork以外のrefを更新していない。
- 開始時/公開時とも空き48G、全63G、使用13G。追加worktree・cache複製なし。
- 使用量枠は不明。公開拒否・結果不明の外部操作・失われた成果は無かった。

本報告とcompleted心拍の後続公開は記録のみでLean sourceを変えない。
後続commitのCIはsource commitのCIと取り違えない。

完了記録の準備時刻: 2026-11-10T09:43:15Z、開始から15.9分。25分以内に部分目標と公開を閉じる。

## 残りのB4橋と次の候補

主要橋は5本のまま:
`source_boundary_adequate`、`generated_work_closed`、`saturate_terminates_and_closes`、
`saturated_frontier_exact`、`resolve_dictionary_order_sound`。
今回閉じたのは橋1の内部にある有限graphのsource model接続。

次の候補:
1. named occurrenceの実計算slotと新source-model入口の対応。元sourceからtable/occurrence/
   templateを導くadequacyを名指しし、任意関数入力を実生成へ置換する。
2. templateが現在ordinary receiverのmaterializationを保存する契約と、sourceの
   関連名/arity/出力bindingを含む生成の橋。Q1/Q2の未決意味を先に選ばない。
3. 未記載moduleの入力監査を続け、I-13の全量調査と単なるmodule言及数を区別する。

## 再現用の境界検査

以下を一時Leanファイルへ保存し、上記focused build後に`lake env lean --trust=0`で検査できる。
production定理を増やすためのmoduleではなく、今回の監査境界を再現するscratchである。

```lean
import Yulang.CommonRoleFiniteAssociatedSourceModels
import Yulang.CommonRoleNamedAssociatedGraph
import Yulang.CommonRoleNamedPath
open Yulang
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
namespace Cycle76BoundaryCheck

def env : Roles.AssocEnv := ⟨[], by simp⟩
def roles : Roles.RoleDecls := fun _ => ⟨0, fun _ => none, by simp⟩
theorem wf : Roles.WellFormed env.cores := by simp [env, Roles.AssocEnv.cores, Roles.WellFormed]
theorem awf : Roles.AssocWellFormed env roles := by simp [env, Roles.AssocWellFormed]

def table : List Nat := [7, 7]
def raw : CommonRoleFiniteAssociatedClosure.Source 2 := ⟨fun _ => 7, []⟩
def splitValues : Fin 2 → Comp Common.model := fun slot =>
  Comp.pure Common.model (if slot.val = 0 then .base .int else .base .str)

-- Scalar cache sharing alone imposes no equality when no scalar facts are present.
example : CommonRoleFiniteAssociatedClosure.saturate env roles wf raw State.empty = [] := by
  decide +kernel
example : (CommonRoleFiniteAssociatedModels.run env roles wf raw State.empty).atoms = [] := by
  decide +kernel
example : All Common.model splitValues
    (CommonRoleFiniteAssociatedModels.run env roles wf raw State.empty).atoms := by
  change All Common.model splitValues []
  exact PresenceNormalForm.all_nil _ _

theorem split_not_coherent : ¬ CommonRoleSourceIdentity.Coherent table splitValues := by
  intro coherent
  have eq := coherent (0 : Fin 2) (1 : Fin 2) rfl
  have impossible : (.int : Inference.Base) = .str :=
    (CommonRigidHeadInspection.base_iff .int .str).mp eq.1
  cases impossible

-- The new entry rejects that split even with an empty associated occurrence list.
example : ¬ All Common.model splitValues
    (CommonRoleFiniteAssociatedSourceModels.run env roles wf table [] State.empty).atoms := by
  intro model
  obtain ⟨_, values, factor⟩ := CommonRoleFiniteAssociatedSourceModels.source_factorization
    env roles wf table [] State.empty splitValues model
  exact split_not_coherent (CommonRoleSourceDescent.factors_coherent table splitValues values factor)

-- It is an iff for every occurrence assignment, not a forced fixed scalar assignment.
example (v : CommonRoleSourceIdentity.Slot table → Comp Common.model) :
    All Common.model v
      (CommonRoleFiniteAssociatedSourceModels.run env roles wf table [] State.empty).atoms ↔
    All Common.model v State.empty.atoms ∧ ∃ sourceValues,
      CommonRoleSourceDescent.Factors table v sourceValues ∧
      ∀ fact, CommonRoleFiniteAssociatedDeclaration.DeclarativeDerives env roles
        (CommonRoleFiniteAssociatedSourceModels.source table [])
        (CommonRoleSourceIdentity.extend table State.empty) fact →
        Common.Equivalent (sourceValues (CommonRoleSourceIdentity.source table fact.1))
          (.base fact.2) :=
  CommonRoleFiniteAssociatedSourceModels.run_source_models_exact env roles wf awf table [] State.empty v

-- The older named allocator computes distinct occurrence positions even for one shared name.
def named : CommonRoleNamedAssociatedGraph.Program :=
  [⟨7, 7, 0, fun _ => ⟨0, []⟩⟩]
example : CommonRoleNamedAssociatedGraph.table named = [7, 7] := rfl
example : CommonRoleNamedAssociatedGraph.receiver named ⟨0, by decide⟩ ≠
    CommonRoleNamedAssociatedGraph.output named ⟨0, by decide⟩ := by decide +kernel
example : CommonRoleNamedAssociatedGraph.identity named (CommonRoleNamedAssociatedGraph.receiver named ⟨0, by decide⟩) =
    CommonRoleNamedAssociatedGraph.identity named (CommonRoleNamedAssociatedGraph.output named ⟨0, by decide⟩) := rfl

-- Existing path inputs may repeat slots and the fixed seed still remains explicit.
example : CommonRoleNamedPath.table 7 [7, 8] = [7, 7, 8] := rfl
example : (CommonRoleNamedPath.outputs 7 [7, 8]).map Fin.val = [1, 2] := by decide +kernel
example : CommonRoleStatefulPathParent.lastSlot ([1, 1] : List (Fin 2)) 0 = 1 := rfl
example : CommonRoleAssociatedStateFlow.scalar (Roles.AssocExamples.box Roles.Examples.str) = none := rfl
example : CommonRoleOrdinaryKnownness.encode .bool = none := rfl
example : CommonRoleOrdinaryKnownness.encode .unit = none := rfl

end Cycle76BoundaryCheck
#print axioms Yulang.CommonRoleFiniteAssociatedSourceModels.run_models_exact
#print axioms Yulang.CommonRoleFiniteAssociatedSourceModels.source_factorization
#print axioms Yulang.CommonRoleFiniteAssociatedSourceModels.run_source_models_exact
#print axioms Yulang.CommonRoleFiniteAssociatedSourceModels.solver_source_exact
#print axioms Yulang.CommonRoleFiniteAssociatedDeclaration.saturate_declaration_exact
#print axioms Yulang.CommonRoleNamedAssociatedGraph.named_exact
#print axioms Yulang.CommonRoleNamedPath.outer_exact
#print axioms Yulang.CommonRoleStatefulPathParent.outer_exact
#print axioms Yulang.CommonRoleAssociatedDeclarationExact.assocOf_exact
```
