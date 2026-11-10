# dots cycle 80 — grouped associated-clause extraction、公開中断からの復旧

## 結果と部分目標

**有限の scope 解決済み where clause 列の全 associated equation を抽出し、検査済み program と独立な source 導出へ双方向で結ぶ部分目標を閉じた。**
`CommonRoleAssociatedClauseExtraction` は237行。任意有限 sourceについて clause/equation の順序と重複を保持し、生成行の出自・網羅性、検査成功/失敗の同値、既存の飽和 evidence/model/solver への接続を証明した。

これは新しい小さな Lean carrier の associated-equation projection であり、Rust parser AST の adequacy でも、空の関連等式を持つ bare role 義務の解決でもない。名前解決・可視性・registry の source 構築、動的 child、一般 interval knownness、最終四分類、辞書順、全言語の主型性は未完。B4 の主要橋は5本のまま。新規意味論の選択0、既存定理の変更0、新規質問0。

## 量化範囲と定理の側

`Equation` は関連名と output source名、`Clause` は receiver source名・構造goal・有限 equation列。`Source` は有限 clause列。`lower` は各 equation を1行に展開する。role registry は既存の total 関数で、scope は一つの placeholder、伝播は既存 int/str scalar 断片。

- `lower_exact`（健全性・完全性）: 任意 source/rowについて、生成列 membership iff 独立 `Occurs` が clause/equation membership から導出される。
- `lower_cons`, `lower_append`（補助）: 任意 clause/source、任意2 sourceの連結は生成列の連結に等しい。重複・順序を保持する。
- `lower_length`（補助）: 任意 sourceの生成行数は各clauseのequation数の総和。
- `lower_position`（補助）: 任意 before/after source、clause、有限範囲内の equation位置 jについて、生成列の offset+j はその equation の row。
- `valid_exact`（健全性・完全性）: 任意 roles/sourceについて、lower の全行が有効 iff 全 source equationがscope/arity/関連名検査を満たす。
- `check_exact`（健全性・完全性）: 任意 roles/source/program pについて、check=some p iff erasure p=lower source かつ source全式が有効。
- `check_accepts`, `check_fails`（健全性・完全性）: 任意 roles/sourceについて、受理 iff 全式有効、失敗 iff 無効な具体的clause/equationが存在。
- `checked_count`, `checked_occurs`（補助／健全性・完全性）: 任意成功検査について、program長は元equation数の総和。任意raw rowについて、program内に同じerasureの行が存在 iff 独立Occurs。
- `step_exact`（健全性・完全性）: 任意env/roles/clause/equation/構造行q/head/resultについて、erase q=row c eなら構造Step iff source Step。後者は独立 Fills/Resolves/AssocDerives とscalar decodingから定義。
- `derives_exact`（健全性・完全性）: 任意env/roles/source、成功検査で得たprogram、任意旧state/source名/headについて、構造Derives iff source clause/equationを直接読む独立Derives。初期seedのinterfaceは検査済みprogramのtableを使う。
- `run_evidence_exact`（健全性・完全性）: 任意env/roles、明示core wf/associated awf、任意成功検査、旧state、table内slot/headについて、実飽和のevidence iff そのslotのsource名に独立Derives。
- `run_source_exact`（健全性・完全性）: 同じwf/awf・成功検査・旧stateと任意assignment vについて、返却atomsのmodel iff 旧atomsのmodelかつ、計算tableを通したsource valuationへのfactorizationと全source Derivesのscalar等式。
- `solver_source_exact`（健全性・完全性）: 同じ前提について、実solverのconsistent=true iff 上のmodel/valuationが存在。

scope/arity/関連名の検査は既存checkerの境界であり、新たな言語の拒否規則ではない。空equation列は空projectionなので不正arityのbare clauseでも抽出checkerは受理し得る。total registryはrole999にもsignatureを与え得る。双方を回帰で明記し、bare roleの解決や可視性検査と取り違えない。

## 実装と台帳

設計ノートを先にcommitした（15dc23c58）。実装commitは6e0e84d60e91ea0a47f00ad55e8b1a74e079f43d。Yulang import、Auditの16定理、README、台帳Q節、coverage TSV、design INDEXを追加。検証済みsourceは復旧時に変更していない。
inventoryはCommonRole247、Main到達93、Audit到達247、台帳言及120。言及数は入力監査完了数ではない。I-13は部分達成で期限超過も残る。

## 検証

復旧担当が独立に以下を再実行し、全てexit 0。全体build/Audit/AxiomGateは実行していない。

```text
cd lean
ELAN_HOME=../../elan ../../elan/bin/lake build Yulang.CommonRoleAssociatedClauseExtraction --wfail
Build completed successfully (289 jobs).
ELAN_HOME=../../elan ../../elan/bin/lake env lean --trust=0 ../../cache/yulang80/boundary-check.lean
exit 0
```

scratchは23 exampleと6 named helper theorem（wf、awf、checked、propagated、sourceStep、sourceDerived）。空source、空equation、多式、重複、逆順、共有source名、不正な途中行、関連名の分離、total registryの限界、実3行飽和を確認。source構成子から2段の独立導出を作り、reverse方向で実飽和evidenceを得る回帰も実行済み。最後の公開前心拍の「22例+4helpers、reverse回帰準備中」は古い状態で、実ファイルと再実行は23例+6helpers。

16定理のtrust=0公理出力全文:

```text
'Yulang.CommonRoleAssociatedClauseExtraction.lower_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAssociatedClauseExtraction.lower_cons' does not depend on any axioms
'Yulang.CommonRoleAssociatedClauseExtraction.lower_append' depends on axioms: [propext]
'Yulang.CommonRoleAssociatedClauseExtraction.lower_length' depends on axioms: [propext]
'Yulang.CommonRoleAssociatedClauseExtraction.lower_position' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAssociatedClauseExtraction.valid_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAssociatedClauseExtraction.check_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAssociatedClauseExtraction.check_accepts' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAssociatedClauseExtraction.check_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAssociatedClauseExtraction.checked_count' depends on axioms: [propext]
'Yulang.CommonRoleAssociatedClauseExtraction.checked_occurs' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAssociatedClauseExtraction.step_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAssociatedClauseExtraction.derives_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAssociatedClauseExtraction.run_evidence_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleAssociatedClauseExtraction.run_source_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleAssociatedClauseExtraction.solver_source_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`python3 tools/boundary-input-inventory.py --check` (exit 0):

```text
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=247; Main=93; Audit=247; ledger mentioned=120. Mention counts are not audit completion counts.
```

`bash tools/verify-lean.sh . origin/integration/m1-final --no-build` (exit 0)の再実行全文:

```text
verify-lean: . @ fdb4e5339 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

`git diff --check` exit 0。公理はpropext/Classical.choice/Quot.soundのみ。remote CIは公開後に別途確認が必要で、ここでは成功を主張しない。
新しいYulang2/Rust parser実行なし。既存C3-PARENTの両順/generic成功とmissing-child拒否は意味論の参考で、このLean carrierの直接oracleではない。

## 中断、復旧、公開、時刻と資源

- 元の開始心拍は11:28:47 UTC。親から指定された期限11:52:19 UTCを超えて公開が停止し、workerが中断された。25分上限と時刻基準心拍を守れたとはしない。
- 最後の公開はa65fbe4dfae9998e541e950fc2b553934f9d5738、11:38:53 UTCのrunning心拍のみ。復旧時点でsource8 pathのblobはすべて404、source moduleも先端で404。保留したAPIの正確な種類は不明だが、公開branchは動いていないと確認した。
- 復旧時にgit/lake/Lean/Pythonの書き込みプロセスが無いことを確認。local-cycle80の3 commitと既存cacheを保持。唯一の未commit変更は心拍の例数修正だった。破壊的操作・cache複製なし。
- live integration/m1-finalは6b25d1929c072262a57b46aae96d5a8590245363でlocal baseと一致。最新inboxはACTIVE。work/dots-main以外は書き込まない。
- 復旧公開は既存8 source/design path、最終報告、crash記録、completed心拍の計11 pathを一括tree/commitにする。既存work headを親にし、expected-head指定・force=falseで更新し、全treeと11 pathのblobを取得照合する。公開の確認はこの記録を書いた後に行い、最終応答で実際の結果を報告する。
- 全体の検証、全Audit、remote CIの確定は監督役に残る。新しいcycleの実装を並行していない。
- 復旧時の空き48G（全63G、使用13G）。元cycle開始時の容量は未確認。使用量枠は不明。
- この記録の作成時刻: 2026-11-10T11:59:09Z。元開始からの経過は30.4分で、期限超過を含む。復旧開始の正確な時刻は未記録。

## 残るB4橋と次候補

`source_boundary_adequate`、`generated_work_closed`、`saturate_terminates_and_closes`、`saturated_frontier_exact`、`resolve_dictionary_order_sound` の5本が未完。

1. この有限associated-equation projectionの外側にある名前解決・可視性・registry構築の具体化。
2. bare role obligationを失わないsource境界とdynamic childへの接続。既存質問を意味論の仮定として隠さない。
3. I-13未監査moduleの入力台帳を続ける。

## 再現用境界検査

```lean
import Yulang.CommonRoleAssociatedClauseExtraction
open Yulang CommonRoleAssociatedClauseExtraction
open CommonRoleSettledConstraints (State)
namespace Cycle80BoundaryCheck

def roles := Roles.AssocExamples.requiredRoles
def env := Roles.AssocExamples.singletonEnv Roles.AssocExamples.boxImpl
theorem wf : Roles.WellFormed env.cores := Roles.AssocExamples.box_paterson
theorem awf : Roles.AssocWellFormed env roles := Roles.AssocExamples.box_assoc_wellFormed

def goal : Roles.Goal := Roles.AssocExamples.index
  (Roles.AssocExamples.box (.var 0)) Roles.Examples.int
def first : Clause := ⟨3, goal, [⟨0, 7⟩, ⟨0, 9⟩]⟩
def second : Clause := ⟨7, goal, [⟨0, 11⟩]⟩
def src : Source := [first, second]
def template : CommonRoleStructuralAssociatedTemplates.Template := ⟨goal, by decide⟩
def p : CommonRoleStructuralAssociatedTemplates.Program :=
  [⟨3, 7, 0, template⟩, ⟨3, 9, 0, template⟩, ⟨7, 11, 0, template⟩]

theorem checked : check roles src = some p := by
  apply (check_exact roles src p).mpr
  exact ⟨rfl, by decide⟩
example : (lower src).length = 3 := by decide
example : (lower [first, first]).length = 4 := by decide
example : (lower [second, first])[0]? = some (row second ⟨0, 11⟩) := by decide
example : (lower [second, first])[2]? = some (row first ⟨0, 9⟩) := by decide
example : (lower [first, first])[0]? = (lower [first, first])[2]? := by decide
example : (check roles []).isSome = true := by decide +kernel
example : (check roles [first, first]).isSome = true := by decide +kernel
example : p.length = 3 := checked_count roles src p checked
example : Occurs src (row first ⟨0, 9⟩) := .equation first ⟨0, 9⟩ (by simp [src]) (by simp [first])
example : (lower ([second] ++ first :: [second]))[(lower [second]).length + 1]? =
    some (row first ⟨0, 9⟩) := lower_position [second] [second] first ⟨1, by decide⟩

def invalidName : Clause := { first with equations := [⟨0, 7⟩, ⟨99, 9⟩, ⟨0, 11⟩] }
def invalidScope : Clause := { first with goal := ⟨2, [.var 1, Roles.Examples.int]⟩ }
def invalidArity : Clause := { first with goal := ⟨2, [.var 0]⟩ }
example : (check roles [invalidName]).isNone = true := by decide +kernel
example : (check roles [first, invalidScope, second]).isNone = true := by decide +kernel
example : (check roles [first, invalidArity]).isNone = true := by decide +kernel
example : ∃ c ∈ [first, invalidName, second], ∃ e ∈ c.equations, ¬ CommonRoleCheckedAssociatedPrograms.Valid roles (row c e) := by
  apply (check_fails roles _).mp
  decide +kernel

-- Empty equations are only an empty projection, not successful bare-role checking.
def bare : Clause := { invalidArity with equations := [] }
example : lower [bare] = [] := rfl
example : (check roles [bare]).isSome = true := by decide +kernel
example : (check roles [{first with goal := ⟨999, [.var 0, Roles.Examples.int]⟩}]).isSome = true := by decide +kernel

def initialSlot : Fin (CommonRoleStructuralAssociatedTemplates.compile p).length := ⟨0, by decide⟩
def lastSlot : Fin (CommonRoleStructuralAssociatedTemplates.compile p).length := ⟨2, by decide⟩
def receiver := CommonRoleNamedAssociatedSourceModels.receiver
  (CommonRoleStructuralAssociatedTemplates.compile p) initialSlot
def output := CommonRoleNamedAssociatedSourceModels.output
  (CommonRoleStructuralAssociatedTemplates.compile p) lastSlot
def initial : State (CommonRoleStructuralAssociatedTemplates.table p).length :=
  CommonRoleCandidateStateFrontier.extend State.empty receiver .str

theorem propagated : CommonRoleOrdinaryKnownness.Evidence
    (CommonRoleStructuralAssociatedTemplates.run env roles wf p initial).atoms output .str := by
  apply (CommonRoleFiniteAssociatedStable.run_evidence env roles wf
    (CommonRoleNamedAssociatedSourceModels.source (CommonRoleStructuralAssociatedTemplates.compile p))
    (CommonRoleNamedAssociatedSourceModels.prepared (CommonRoleStructuralAssociatedTemplates.compile p) initial)
    output .str).mpr
  apply (CommonRoleFiniteAssociatedClosure.saturate_exact env roles wf _ _ (output, .str)).mp
  decide +kernel
example : Derives env roles src p initial 11 .str :=
  (run_evidence_exact env roles wf awf src p checked initial output .str).mp propagated

-- Build a source derivation from source constructors, then use the reverse bridge.
theorem sourceStep : Step env roles first ⟨0, 7⟩ .str .str := by
  refine ⟨Roles.Examples.str, Roles.AssocExamples.index
    (Roles.AssocExamples.box Roles.Examples.str) Roles.Examples.int,
    rfl, rfl, ?_, ?_, Roles.Examples.str, ?_, rfl⟩
  · exact .cons (.app (.cons .hole .nil)) (.cons (.app .nil) .nil)
  · exact (RoleConstraints.resolve_exact _ wf _).mp Roles.AssocExamples.box_resolved
  · exact Roles.AssocDerives.explicit Roles.AssocExamples.boxImpl
      (fun _ => Roles.Examples.str) (by simp [env, Roles.AssocExamples.singletonEnv])
      rfl rfl (by simp [Roles.AssocExamples.boxImpl]) (.var 0) rfl

theorem sourceDerived : Derives env roles src p initial 11 .str := by
  apply Derives.equation (head := .str) second ⟨0, 11⟩ (by simp [src]) (by simp [second])
  · apply Derives.equation (head := .str) first ⟨0, 7⟩ (by simp [src]) (by simp [first])
    · exact .initial ⟨receiver, rfl, by simp [CommonRoleOrdinaryKnownness.Evidence, initial, CommonRoleCandidateStateFrontier.extend, CommonRoleCandidateStateFrontier.equality]⟩
    · exact sourceStep
  · exact sourceStep
example : CommonRoleOrdinaryKnownness.Evidence
    (CommonRoleStructuralAssociatedTemplates.run env roles wf p initial).atoms output .str :=
  (run_evidence_exact env roles wf awf src p checked initial output .str).mpr sourceDerived

-- Distinct associated names retain separate outputs and reject only undeclared names.
def twoDecl : Roles.RoleDecl where
  arity := 2
  assoc := fun n => if n < 2 then some none else none
  defaultsScoped := by intro n rhs h; split at h <;> simp_all
def twoRoles : Roles.RoleDecls := fun _ => twoDecl
def twoNames : Clause := { first with equations := [⟨0, 7⟩, ⟨1, 9⟩] }
example : (check twoRoles [twoNames]).isSome = true := by decide +kernel
example : (lower [twoNames])[0]? = some ⟨3, 7, 0, goal⟩ := rfl
example : (lower [twoNames])[1]? = some ⟨3, 9, 1, goal⟩ := rfl
example : (check roles [twoNames]).isNone = true := by decide +kernel

end Cycle80BoundaryCheck
#print axioms Yulang.CommonRoleAssociatedClauseExtraction.lower_exact
#print axioms Yulang.CommonRoleAssociatedClauseExtraction.lower_cons
#print axioms Yulang.CommonRoleAssociatedClauseExtraction.lower_append
#print axioms Yulang.CommonRoleAssociatedClauseExtraction.lower_length
#print axioms Yulang.CommonRoleAssociatedClauseExtraction.lower_position
#print axioms Yulang.CommonRoleAssociatedClauseExtraction.valid_exact
#print axioms Yulang.CommonRoleAssociatedClauseExtraction.check_exact
#print axioms Yulang.CommonRoleAssociatedClauseExtraction.check_accepts
#print axioms Yulang.CommonRoleAssociatedClauseExtraction.check_fails
#print axioms Yulang.CommonRoleAssociatedClauseExtraction.checked_count
#print axioms Yulang.CommonRoleAssociatedClauseExtraction.checked_occurs
#print axioms Yulang.CommonRoleAssociatedClauseExtraction.step_exact
#print axioms Yulang.CommonRoleAssociatedClauseExtraction.derives_exact
#print axioms Yulang.CommonRoleAssociatedClauseExtraction.run_evidence_exact
#print axioms Yulang.CommonRoleAssociatedClauseExtraction.run_source_exact
#print axioms Yulang.CommonRoleAssociatedClauseExtraction.solver_source_exact
```
