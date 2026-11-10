# dots cycle 77 — 計算されたnamed allocationと独立source名導出

## 結果と部分目標

**有限named associated programのslot割当と、source名上の独立導出・ordinary modelの
接続を閉じた。** cycle76の外部tableとoccurrence slot mapを、既存named allocatorから
計算する入口を作った。独立`NamedDerives`は元stateのscalar seedと宣言由来の
associated stepだけを持ち、実resolverの返却値や飽和済み集合を参照しない。

[ソース公開436259c0](https://github.com/momota1029/yulang/commit/436259c0f3e804c02bff55a718f5b7a93d3fb89c)
のtree `d73bbfd5033895a19ffaa364c681b1f5b2517c9c` はlocal検証commit
`36e2eb248d67949bbc9b7fedac14259cd20a02cf` のtreeと完全一致する。
remote recursive treeの全2287entryと、変更9pathのblob SHAを再取得・照合した。

source seedを追加するordinary identityはvar-var等式なので、元stateにない明示scalar
Evidenceを作らないことも証明した。source名の導出は、計算slotの独立導出と双方向で
一致する。最終stateのscalar Evidence、全assignmentのordinary model、実ordinary solverの
受理をその独立source名導出へ接続した。

有限programの任意サイズ、枝分かれ、重複、同名、cycleを扱う。一般の実ソースから
そのprogramとtemplateを導くadequacy、動的where、一般区間knownness、四方向分類、
辞書順、全言語の主型性は証明していない。B4の主要橋は5本のまま。
新しい言語意味の採用0、既存定理の変更0、新規質問0。

## 量化範囲と新規定理

新規モジュールは`CommonRoleNamedAssociatedSourceModels`（202行）。
共通入力はenv/roles、任意の有限`p : Program`、任意の旧
`s : State (table p).length`。pの各行はscope解決済みreceiver/output名、関連名、
base→goalのtemplateを持つ。table、全endpoint slot、source identityはpから計算する。

- `receiver_source`、`output_source`（補助）: 任意pと行indexについて、計算slotの
  source名が元のreceiver/output名に一致する。
- `prepared_evidence`（補助、両方向）: 任意p/s/slot/headについて、ordinary identityを
  追加する前後の明示scalar Evidenceは同値。一般の意味的含意全体の主張ではない。
- `allocated_to_named`（健全性）: 任意env/roles/p/s/factのslot上の独立導出は、
  そのfactのsource名上のNamedDerivesへ移る。
- `named_to_allocated`（完全性）: 任意env/roles/p/s/name/headのNamedDerivesがあれば、
  そのnameを表す任意の計算slotで、slot上の独立導出が得られる。
- `allocated_named_exact`（健全性・完全性）: 上二つを任意factのiffにまとめる。
- `named_support`（補助）: 任意のNamedDerivesについて、その名前を持つ計算slotが存在。
  tableに無い名前へ等式を課さない。ここまでの独立判断の橋にwf/awfは不要。
- `run_evidence_exact`（健全性・完全性）: 任意env/rolesに明示core well-formedness wf、
  associated well-formedness awfを加え、任意p/s/slot/headについて、返却stateの
  実scalar detector Evidence iff source名のNamedDerives。
- `run_source_exact`（健全性・完全性）: 同じwf/awfと任意p/s、全assignment vについて、
  返却stateのmodel iff 元sのmodelかつ、一つのsource型valuationへfactorし、
  全NamedDerivesのscalar等式を満たすvaluationが存在する。
- `solver_source_exact`（健全性・完全性のsolver接続）: 同じ入力の実ordinary solverが
  consistent=true iff 上記を満たすassignmentとsource valuationが存在する。

source valuation、成功、model、燃料、完成したfrontierはcallerの実行前提ではない。
effect行の同一性は追加せず、既存のtype/effect制約は保持する。
有限named programとtemplateが入力であることは実装断片の境界であり、仕様の拒否規則でない。

## I-13と設計境界

台帳N節へ全新規入力と上記10定理の依存、残る生成義務を追加した。
この断片ではM4に残っていたtable/slot mapを計算できたが、source scopingと
invocationの同一性、templateのreceiver/引数materialization、registry可視性とwf/awfの
source検査は外側に残る。Q1/Q2、cycle23/24の既存質問を未決のまま維持する。

inventoryはCommonRole 244、Main到達93、Audit到達244、台帳言及117。
**言及数は全入力監査済み数ではない。I-13は部分達成で、cycle72期限超過は解消しない。**

設計ノートは`notes/design/2026-11-10-cycle77-named-associated-source-models.md`。
開始時に部分目標を心拍へ書いたが、詳細設計ノートの保存は最初のLean試作後となった。
設計先行の保存順を守れていなかったので、次回は試作前に短い型と境界を保存する。

## 検証

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build --wfail Yulang.CommonRoleNamedAssociatedSourceModels
Build completed successfully (286 jobs).
exit 0

ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang77/boundary-check.lean
exit 0
```

scratchは17境界assertionと、既存well-formedness定理の2aliasを含む計19宣言。
中間心拍の「19境界assertion」はこの2aliasも数えていたため、この報告で訂正する。
新規10定理の公理出力はpropext / Classical.choice / Quot.soundのみ。

検査した主な境界:
1. `[3,7,7,9]`の計算tableと4endpoint位置。同名7でもslotは異なる。
2. 実finite saturationがstr seedを第一行、共有7、第二行を経て出力9へ伝播し、
   その結果に独立NamedDerivesがある。
3. 任意env/roles/有限programについて、空stateではNamedDerivesを生成できない。
   constant known goal templateを使う自己cycleも、seedを無から作れない。
4. 同名の二slotへint/strを割り当てる分裂modelは拒否される。
5. tableに無い名前99への独立導出は無い。空programは空table/空返却atomsになる。

最初のproduction試作ではidentity等式の型の明示とassociatedのq推論が不足して
ビルドが失敗した。型を明示して修正し、最終版は上記focused buildで通過。
scratch初回はAtomのDecidableEqが無いため直接decisionできなかった。既存の
計算可能なFact membershipをkernelで検査し、検証済みEvidence橋へ通す形へ変更した。
未提供のtacticと省略引数の推論も明示した。期待する結果を弱めず全件再検査した。

`python tools/boundary-input-inventory.py --check`と`git diff --check`はexit 0。
`bash tools/verify-lean.sh . origin/integration/m1-final --no-build`の全文（exit 0）:

```text
verify-lean: . @ 36e2eb248 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

dotの環境では全体lake build、全Audit/AxiomGate、build付きverify-leanを実行していない。
公開source commit `436259c0f3e804c02bff55a718f5b7a93d3fb89c`のCIは両方success:
- [Core CI](https://github.com/momota1029/yulang/actions/runs/42796413681)。
- [Lean inference kernel](https://github.com/momota1029/yulang/actions/runs/42796413872)。
  10:08:47 UTC時点でcompleted/success。build、全宣言監査、例実行stepを含む。
後続記録commitのCIと取り違えず、このsource commitに対する結果として記録する。

## Yulang2との照合

live work/dots-audit `55574b6052ef1534fd0fc36d6d3617ebede59a0e` のx-oracleを再取得した。
C3-PARENTのleft/right両順とgeneric functionの(11,22)、missing-child拒否、
X13〜X16の局所区間結果を参照した。spec6.2/6.3のsource共有・関連型等式の素材として
使い、内部allocator/NamedDerives/templateの直接oracleとは見なさない。
新しいYulang2実機やparser実行はしていない。

## 開始、復旧、公開、資源

- トリガー開始09:57:19 UTC、最初のdate記録09:57:28。
- integration/workのlive headはどちらもf54542625。standing-orders/inboxを再読。
  ACTIVE、上限なし、I-11の25分上限、全体build禁止を適用。
- cycle76はcompletedで報告も存在し、crash復旧は不要。
  一つの既存作業場とbuild cacheを使い、API統合版からlocal-cycle77を作成。
  旧local履歴は保持し、追加worktree/cache複製や破壊的な削除はしていない。
- 開始心拍は20c6525b、API commit時刻09:58:03。初回updatedに手入力した09:59:08は
  commit時刻より先になっていた。以後はUTC dateから生成し、source公開時に訂正した。
- 9pathのsource/notes/心拍を一つのtree/commitにまとめ、10:07:04に公開commitを作成。
  workだけをforce=false、expected_sha=20c6525b…で更新。開始から約9.8分で公開した。
  9blobはlocal内容hashと照合。baseは最新API treeを使い、未変更pathを保全した。
- source treeを再取得し、全treeと全9変更blobを検証した。
- 10分心拍はfe716e13。source後の心拍/報告更新はLeanを変更しない。
- 大きなlocal payloadを一度のreadで取得しようとして出力が切れ、JSON parseに失敗。
  その段階ではAPI書き込み前。以後はpinned integrationの内容とappend-only差分を
  組み合わせ、作成blobの全SHAを照合して一つのtreeへまとめた。拒否回避ではない。
- 開始時/公開時の空き48G、全63G、使用13G。使用量枠は不明。
- 公開拒否、結果不明の外部操作、失われた成果は無かった。

完了記録の準備時刻: 2026-11-10T10:10:36Z、開始から13.3分。
25分以内に一つの部分目標と検証済み公開を閉じた。報告とcompleted心拍は記録のみで、
Lean sourceを変更しない。source9pathに本報告1pathを加え、cycle全体は10path。

## 残りのB4橋と次の候補

主要橋は5本のまま:
`source_boundary_adequate`、`generated_work_closed`、`saturate_terminates_and_closes`、
`saturated_frontier_exact`、`resolve_dictionary_order_sound`。
今回閉じたのは橋1内部の、有限named allocatorと独立source名modelの接続。

次の候補:
1. `template`の生成側で、現在receiverのmaterialization、role/name/arity、出力bindingが
   sourceに一致する契約を具体化する。任意関数入力のまま全sourceのadequacyとしない。
2. sourceのwhere/associated構文から有限named programを生成し、全occurrenceの出自と
   網羅性を示す。動的生成とQ1/Q2の未決事項を先に選ばない。
3. I-13未記載moduleの入力監査を継続し、言及数と全入力監査済みを引き続き区別する。

## 再現用の境界検査

以下をscratch Lean fileへ保存し、上記focused build後に`lake env lean --trust=0`で実行する。
本番定理を増やすためのmoduleではなく、今回の境界を再現する検査である。

```lean
import Yulang.CommonRoleNamedAssociatedSourceModels
open Yulang
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
namespace Cycle77BoundaryCheck
open CommonRoleNamedAssociatedSourceModels
open CommonRoleNamedAssociatedGraph (Program table)

def env := Roles.AssocExamples.singletonEnv Roles.AssocExamples.boxImpl
def roles := Roles.AssocExamples.requiredRoles
theorem wf : Roles.WellFormed env.cores := Roles.AssocExamples.box_paterson
theorem awf : Roles.AssocWellFormed env roles := Roles.AssocExamples.box_assoc_wellFormed

def template (head : Inference.Base) : Roles.Goal :=
  Roles.AssocExamples.index
    (Roles.AssocExamples.box (.app (if head = .str then 1 else 0) [])) Roles.Examples.int

def program : Program := [⟨3, 7, 0, template⟩, ⟨7, 9, 0, template⟩]
def first : Fin program.length := ⟨0, by decide⟩
def second : Fin program.length := ⟨1, by decide⟩
def initial : State (table program).length :=
  CommonRoleCandidateStateFrontier.extend State.empty (receiver program first) .str

-- Computed slots remain distinct while the intervening source name is shared.
example : table program = [3, 7, 7, 9] := by decide +kernel
example : (receiver program first).val = 0 := rfl
example : (output program first).val = 1 := rfl
example : (receiver program second).val = 2 := rfl
example : (output program second).val = 3 := rfl
example : output program first ≠ receiver program second := by decide +kernel
example : CommonRoleSourceIdentity.source (table program) (output program first) =
    CommonRoleSourceIdentity.source (table program) (receiver program second) := rfl

-- The real finite computation propagates across different occurrences of name 7.
theorem propagated : CommonRoleOrdinaryKnownness.Evidence
    (run env roles wf program initial).atoms (output program second) .str := by
  apply (CommonRoleFiniteAssociatedStable.run_evidence env roles wf
    (source program) (prepared program initial) (output program second) .str).mpr
  apply (CommonRoleFiniteAssociatedClosure.saturate_exact env roles wf
    (source program) (prepared program initial) (output program second, .str)).mp
  decide +kernel
example : NamedDerives env roles program initial 9 .str := by
  exact (run_evidence_exact env roles wf awf program initial (output program second) .str).mp propagated

-- No initial evidence means no fact, regardless of associated declarations/templates.
theorem empty_no_named (e : Roles.AssocEnv) (r : Roles.RoleDecls) (p : Program)
    (name : Nat) (head : Inference.Base) :
    ¬ NamedDerives e r p State.empty name head := by
  intro derived
  induction derived with
  | initial seed =>
    obtain ⟨_, _, evidence⟩ := seed
    simp [CommonRoleOrdinaryKnownness.Evidence, State.empty] at evidence
  | associated _ _ _ ih => exact ih
example : ¬ NamedDerives env roles program State.empty 9 .str := empty_no_named env roles program 9 .str
example : ¬ CommonRoleOrdinaryKnownness.Evidence
    (run env roles wf program State.empty).atoms (output program second) .str := by
  rw [run_evidence_exact env roles wf awf]
  exact empty_no_named env roles program _ .str

-- A cycle cannot conjure its seed from a constant known goal template.
def cyclic : Program := [⟨4, 4, 0, fun _ => template .str⟩]
example : ¬ NamedDerives env roles cyclic State.empty 4 .str := empty_no_named env roles cyclic 4 .str

-- Source identity excludes split ordinary assignments even without scalar facts.
def split : CommonRoleSourceIdentity.Slot (table cyclic) → Comp Common.model :=
  fun slot => Comp.pure Common.model (if slot.val = 0 then .base .int else .base .str)
example : ¬ All Common.model split (run env roles wf cyclic State.empty).atoms := by
  intro models
  obtain ⟨_, values, factors, _⟩ := (run_source_exact env roles wf awf cyclic State.empty split).mp models
  have coherent := CommonRoleSourceDescent.factors_coherent (table cyclic) split values factors
  have same := coherent (receiver cyclic ⟨0, by decide⟩) (output cyclic ⟨0, by decide⟩) rfl
  have impossible : (.int : Inference.Base) = .str :=
    (CommonRigidHeadInspection.base_iff .int .str).mp same.1
  cases impossible

-- Absent names have no independent derivation, including with a nonempty seed.
example : ¬ NamedDerives env roles program initial 99 .str := by
  intro derived
  obtain ⟨slot, same⟩ := named_support env roles program initial 99 .str derived
  have bound : slot.val < 4 := slot.isLt
  have cases : slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 2 ∨ slot.val = 3 := by omega
  rcases cases with h | h | h | h <;> simp [CommonRoleSourceIdentity.source, table,
    CommonRoleNamedAssociatedGraph.identity, program, h] at same

-- Empty programs are accepted and allocate no occurrence positions.
example : table ([] : Program) = [] := rfl
example : (run env roles wf [] State.empty).atoms = [] := by decide +kernel

end Cycle77BoundaryCheck
#print axioms Yulang.CommonRoleNamedAssociatedSourceModels.receiver_source
#print axioms Yulang.CommonRoleNamedAssociatedSourceModels.output_source
#print axioms Yulang.CommonRoleNamedAssociatedSourceModels.prepared_evidence
#print axioms Yulang.CommonRoleNamedAssociatedSourceModels.allocated_to_named
#print axioms Yulang.CommonRoleNamedAssociatedSourceModels.named_to_allocated
#print axioms Yulang.CommonRoleNamedAssociatedSourceModels.allocated_named_exact
#print axioms Yulang.CommonRoleNamedAssociatedSourceModels.named_support
#print axioms Yulang.CommonRoleNamedAssociatedSourceModels.run_evidence_exact
#print axioms Yulang.CommonRoleNamedAssociatedSourceModels.run_source_exact
#print axioms Yulang.CommonRoleNamedAssociatedSourceModels.solver_source_exact

```
