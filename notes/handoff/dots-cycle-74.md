# dots cycle 74 — interval/frontierの境界入力監査

## 結果と範囲

**部分目標は閉じた。区間候補・有限構造展開・辞書からordinary graphへの受渡しの16モジュールを監査し、22回帰で境界を確認した。成果はlocalのみ。**

- 台帳 `notes/design/2026-11-10-boundary-inputs-ledger.md` K1〜K4を追加。
  各入力の名前・型・依存定理と、spec4.3/6.2/6.3/6.5からの導出案を記録した。
- 既存inventoryは242モジュール、Mainから93、Auditから242。
  台帳の名前出現は85から99へ増えた。**名前出現数は全入力監査完了数ではない。**
- production Lean変更0、新規production定理0、新規質問ノート0。
  scratchには22のexampleと、それらの証明を共有するhelperを1本置いた。
- docs commit: `9652c1b6e2c76694d0f38b45f112c202f5e3d310`。
- I-13は依然部分達成。cycle72までの公開期限は満たしていない。
  B4の主要5橋、M1全体の健全性・完全性・主型性は未達。

## 有用な境界

1. 構造辞書の`prepared`はordinary解決成功ではない。変数headに対し、
   `int ≤ tick int`という矛盾した元区間でもpreparedになることと、その区間が
   ordinaryモデルを持たないことをLeanで両方確認した。既存定理の誤りではなく、
   そのDictionaryが元々構造的な証拠しか要求しないことを明確にした。
2. 非線形headの低位capture helperは同名bindingを複数返すが、公開inspectは
   linear grammarの外とする。helperの成功を一般の非線形解決と呼ばない。
3. grammar外の宣言は別roleでもscan全体を`none`にする。これは局所実装の保守的な
   範囲外であって、別roleがYulangの解決を妨害するという仕様ではない。
4. 同じ完全な宣言recordはdistinctで一つになるが、異なるkeyは別候補のまま。
   sourceの別implを同じrecordに潰さないidentity生成が必要。
5. record intervalの`.emptyRecord`終端と`.exactEmpty`終端を混同しない。
   closedラベルgateの成功と、返されたpayload atomsの充足も別。
6. graph compilerは実際のgraphを内部生成し任意モデルを反映するが、subtype edgesは
   未解決の義務である。任意name mapの下でのiffは、source同一性の正しさを保証しない。

既存Q1（invocation共有）/Q2（関連型糖衣の検査）を再利用し、新たな言語規則は採用していない。
上記の観察を、新しい言語拒否条件や一般B4反例として扱わない。

## 再開・最新指示

起動予定は2026-11-10T07:57:00Z。最初のdate記録は07:58:11Z。
開始時点のlocal HEAD `c4043b524bc298830fcfccf731900d57a92e5fe6`、
cycle73 completed心拍と報告を確認し、cycle69〜73の成果を全保持した。
前回はlocalで正常完了しており、今回crash報告を作る理由は無い。

`git fetch origin integration/m1-final work/dots-main work/dots-audit`を実行。
GitHubアプリでも最新integration/work、standing orders、inbox、remote心拍とcycle68報告を取得した。
最初のAPI branch URLでslashをpercent encodeした取得はinvalid pathだったため、
通常のslash表記のread-only URLで取り直した。

- integration: `434d3ceefce3bc2dbd8d5cb5d84c6295a9c40cf8`。
  local HEADの祖先、取込済みなのでmergeを重ねていない。
- workのAPI live head: `872066861d13cfa1784bffdaa7bfbb973998c00f`。
  心拍はcycle68 completedで対応する報告も存在。
- transportのorigin/work/dots-mainは古い`822c4cc50a80eb0f1ec22af12070b4905212fd4d`。
  これをAPI公開状態の代わりに使わない。
- standing orders blob: `7ae4d68d2ac7df80d1eadbd061dadd2296faf4c4`。
- inbox blob: `cfe2889a742267063297c3d739cfdb9a92fbeaa3`、ACTIVE、末尾I-13。
  両fileのlocal hash-objectがAPIのblobと一致。STOPではない。

## 検証

環境はLean v4.35.0。`ELAN_HOME=/workspace/scratch/1d0b4aaa3394/elan`と
`PATH=$ELAN_HOME/bin:$PATH`を使用。各Lean実行はtimeout 5m、短いyieldで戻し、
sessionから完了コードを回収した。一つの作業場と既存cacheを再利用した。

### 焦点ビルド

```sh
cd lean
timeout 5m lake build Yulang.CommonRoleIntervalCandidateFrontier Yulang.CommonRoleClosedIntervalInspection Yulang.CommonRoleClosedIntervalRecordGeneration Yulang.CommonRoleIntervalRecordGeneration Yulang.CommonRoleIntervalDictionaryCompilation Yulang.CommonRoleIntervalReadyChain --wfail
```

exit 0、310 jobs。出力全文:

```text
✔ [277/310] Built Yulang.CommonRoleIntervalRecordResidual (808ms)
✔ [278/310] Built Yulang.CoreLiteral (973ms)
✔ [279/310] Built Yulang.CommonRowDeclarations (1.2s)
✔ [280/310] Built Yulang.CommonBoundRefWorklistRows (1.3s)
✔ [281/310] Built Yulang.CommonRoleIntervalExpansion (1.6s)
✔ [282/310] Built Yulang.CasePatternSafety (1.7s)
✔ [283/310] Built Yulang.CommonRoleIntervalRecordGeneration (1.0s)
✔ [284/310] Built Yulang.CommonBoundRefRowDeclarations (919ms)
✔ [285/310] Built Yulang.CommonRoleIntervalCandidateFrontier (2.2s)
✔ [286/310] Built Yulang.CommonRoleIntervalExpansionChecks (1.1s)
✔ [287/310] Built Yulang.CaseEvaluation (1.2s)
✔ [288/310] Built Yulang.CommonBoundRefSolver (992ms)
✔ [289/310] Built Yulang.CoreCommonData (3.4s)
✔ [290/310] Built Yulang.CommonRoleIntervalDictionaries (875ms)
✔ [291/310] Built Yulang.CommonSolvedSource (635ms)
✔ [292/310] Built Yulang.CommonRoleIntervalDictionaryCompilation (640ms)
✔ [293/310] Built Yulang.CommonCoreNamedCase (584ms)
✔ [294/310] Built Yulang.CaseDataTerms (1.6s)
✔ [295/310] Built Yulang.CommonCoreStrictApplication (615ms)
✔ [296/310] Built Yulang.ScopedCasePatterns (4.7s)
✔ [297/310] Built Yulang.CommonPatternLookup (630ms)
✔ [298/310] Built Yulang.CommonPatternConcreteRecordTypes (1.2s)
✔ [299/310] Built Yulang.CommonRoleClosedRecordResidual (529ms)
✔ [300/310] Built Yulang.CommonRoleClosedIntervalRecordGeneration (563ms)
✔ [301/310] Built Yulang.CoreCommonSyntax (4.3s)
✔ [302/310] Built Yulang.CommonRoleClosedRecordComparison (2.6s)
✔ [303/310] Built Yulang.CommonRoleClosedRecordInspection (549ms)
✔ [304/310] Built Yulang.CommonRoleClosedIntervalInspection (492ms)
✔ [305/310] Built Yulang.CoreCommonSyntaxExact (10s)
✔ [306/310] Built Yulang.CommonSolvedCoreSyntax (465ms)
✔ [307/310] Built Yulang.CoreCommonInference (503ms)
✔ [308/310] Built Yulang.CommonDemandSolver (504ms)
✔ [309/310] Built Yulang.CommonRoleDeferredBounds (507ms)
✔ [310/310] Built Yulang.CommonRoleIntervalReadyChain (454ms)
Build completed successfully (310 jobs).
```

### 回帰22件と既存定理の公理確認12件

```sh
cd lean
timeout 5m lake env lean ../../cache/yulang74/boundary-check.lean
```

最終exit 0。公理は全12件ともpropext / Classical.choice / Quot.soundの範囲内。
初回は3つのdependent entryの結果をdecideで簡約できず、型aliasの修飾名も1箇所誤った。
次のsimpによる試行も再帰式の展開が循環しexit1。命題や期待値を弱めず、
既存`scan_exact`と`elaborate_prepared_exact`から辞書証拠を構成する証明へ直して成功した。
productionソースは変更していない。再実行可能な本文:

```lean
import Yulang.CommonRoleIntervalCandidateFrontier
import Yulang.CommonRoleClosedIntervalInspection
import Yulang.CommonRoleClosedIntervalRecordGeneration
import Yulang.CommonRoleIntervalRecordGeneration
import Yulang.CommonRoleIntervalDictionaryCompilation
import Yulang.CommonRoleIntervalReadyChain
open Yulang
open CommonRoleCaptureNormalization (Form)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open Core.PresenceGeneration (TyTerm)
namespace Cycle74BoundaryCheck
def linear : Declaration := ⟨0, 10, [.var 0], []⟩
def nonlinear : Declaration := ⟨1, 11, [.pair (.var 0) (.var 0)], []⟩
def intGoal : Goal := ⟨0, [(.int, .int)]⟩
def inconsistentGoal : Goal := ⟨0, [(.int, .tick .int)]⟩
def prepared : CommonRoleIntervalDictionaries.Answer → Bool
  | .prepared _ _ => true
  | _ => false
example : CommonRoleIntervalCapture.capture (.pair (.var 0) (.var 0))
    (.pair .int (.tick .int), .pair .int (.tick .int)) =
    some [(0, (.int, .int)), (0, (.tick .int, .tick .int))] := rfl
example : CommonRoleIntervalCapture.total
    [(0, (.int, .int)), (0, (.tick .int, .tick .int))] 0 = (.int, .int) := rfl
example : CommonRoleIntervalCapture.supported nonlinear = false := rfl
example : CommonRoleIntervalCandidates.inspect nonlinear intGoal = none := rfl
example : CommonRoleIntervalCandidates.scan intGoal [linear, nonlinear] = none := rfl
example : CommonRoleIntervalCandidates.scan intGoal [nonlinear, linear] = none := rfl
example : CommonRoleIntervalCandidates.inspect
    ⟨0, 12, [.int], []⟩ ⟨0, [(.tick .int, .tick .int)]⟩ = some none := rfl
example : CommonRoleIntervalCandidates.inspect
    ⟨0, 12, [.int], []⟩ ⟨0, [(.var 3, .var 3)]⟩ = none := rfl
example : CommonRoleIntervalCandidates.inspect linear inconsistentGoal =
    some (some [(0, (.int, .tick .int))]) := rfl
theorem prepared_from_single (declarations : List Declaration) (goal : Goal)
    (bindings : CommonRoleIntervalCapture.Bindings)
    (checked : CommonRoleIntervalExpansion.Checked declarations)
    (single : CommonRoleIntervalCandidates.scan goal (Roles.distinct declarations) =
      some [⟨linear, bindings⟩]) :
    prepared (CommonRoleIntervalDictionaries.elaborate declarations goal) = true := by
  let dictionary : CommonRoleIntervalDictionaries.Dictionary declarations goal :=
    .node ⟨linear, bindings⟩ ((CommonRoleIntervalCandidates.scan_exact _ _ _).mp single)
      (fun requirement member => by simp [linear] at member)
  have returned := (CommonRoleIntervalDictionaries.elaborate_prepared_exact declarations goal
    dictionary.erase dictionary.trace).mpr ⟨checked, dictionary, rfl, rfl⟩
  rw [returned]
  rfl
example : prepared (CommonRoleIntervalDictionaries.elaborate [linear] inconsistentGoal) = true := by
  apply prepared_from_single _ _ [(0, (.int, .tick .int))]
  · intro declaration member
    simp only [List.mem_singleton] at member
    subst declaration
    rfl
  · rfl
example : prepared (CommonRoleIntervalDictionaries.elaborate [linear, linear] intGoal) = true := by
  apply prepared_from_single _ _ [(0, (.int, .int))]
  · intro declaration member
    have same : declaration = linear := by simpa using member
    subst declaration
    rfl
  · rfl
example : prepared (CommonRoleIntervalDictionaries.elaborate
    [linear, ⟨0, 99, [.var 0], []⟩] intGoal) = false := by
  cases result : CommonRoleIntervalDictionaries.elaborate
      [linear, ⟨0, 99, [.var 0], []⟩] intGoal with
  | invalidDeclarations => rfl
  | incomplete trace => rfl
  | prepared plan trace =>
    obtain ⟨_, dictionary, _, _⟩ :=
      (CommonRoleIntervalDictionaries.elaborate_prepared_exact _ _ _ _).mp result
    cases dictionary with
    | node candidate unique children =>
      have selected := (CommonRoleIntervalCandidates.scan_exact _ _ _).mpr unique
      have two : CommonRoleIntervalCandidates.scan intGoal
          (Roles.distinct [linear, ⟨0, 99, [.var 0], []⟩]) =
          some [⟨linear, [(0, (.int, .int))]⟩,
            ⟨⟨0, 99, [.var 0], []⟩, [(0, (.int, .int))]⟩] := rfl
      rw [two] at selected
      simp at selected
example : CommonRoleStablePaterson.check CommonRoleIntervalReadyChain.growingDeclaration = false :=
  CommonRoleIntervalReadyChain.growing_rejected
example : CommonRoleIntervalGeneration.generate
    ([(TyTerm.base .int, .base .int), (.base .str, .base .str)] :
      List (CommonRoleIntervalGeneration.Argument Empty)) =
    [.tyLe (.base .int) (.base .int), .tyLe (.base .int) (.base .str),
     .tyLe (.base .str) (.base .int), .tyLe (.base .str) (.base .str)] := rfl
example : CommonRoleIntervalRecordGeneration.recordTerm ([] : List (Nat × TyTerm Empty)) = .emptyRecord := rfl
example : CommonRoleClosedIntervalRecordGeneration.recordTerm ([] : List (Nat × TyTerm Empty)) = .exactEmpty := rfl
example : CommonRoleCanonicalRows.capture []
    ([(1, (TyTerm.base .int, .base .str)), (1, (.base .str, .base .int))] :
      CommonRoleIntervalRecordResidual.Fields Empty) = [(1, (.base .int, .base .str))] := rfl
example : CommonRoleClosedIntervalInspection.reconcile
    ([(1, (TyTerm.base .int, .base .int))] : CommonRoleIntervalRecordResidual.Fields Empty)
    [(2, (.base .int, .base .int))] = none := rfl
example : CommonRoleIntervalDictionaryCompilation.lower (fun _ => (0 : Fin 1)) (.var 3) =
    CommonRoleIntervalDictionaryCompilation.lower (fun _ => (0 : Fin 1)) (.var 99) := rfl
example : CommonRoleIntervalExpansionChecks.intervalChecks (n := 0) inconsistentGoal.arguments =
    [.check Form.int (.tick .int)] := rfl
example : ¬ CommonRoleIntervalExpansionChecks.ConsistentArguments
    (Form.eval (fun _ => (.base .int : Common.Ty))) inconsistentGoal.arguments := by
  intro consistent
  have bad := consistent (.int, .tick .int) (by simp [inconsistentGoal])
  exact CommonRigidHeadInspection.rigid_mismatch rfl rfl (by decide) (by decide) (by decide) bad
example : ∀ (s : CommonRoleSettledConstraints.State n) (slot : Fin n)
    (c : CommonRoleCandidateStateFrontier.Candidate),
    CommonRoleIntervalCandidateFrontier.Fits s ⟨slot, slot⟩ c ↔
      CommonRoleCandidateStateFrontier.Fits s slot c :=
  CommonRoleIntervalCandidateFrontier.same_slot_exact
#print axioms CommonRoleIntervalCapture.capture_arguments_exact
#print axioms CommonRoleIntervalCandidates.scan_exact
#print axioms CommonRoleIntervalCandidates.accepted_child_decreases
#print axioms CommonRoleIntervalExpansion.run_tree_exact
#print axioms CommonRoleIntervalDictionaries.elaborate_prepared_exact
#print axioms CommonRoleIntervalDictionaries.Dictionary.erase_unique
#print axioms CommonRoleIntervalDictionaryCompilation.compile_trace_exact
#print axioms CommonRoleIntervalCandidateFrontier.solutions_exact
#print axioms CommonRoleIntervalGeneration.generate_real_argument_exact
#print axioms CommonRoleClosedIntervalRecordGeneration.compile_exact
#print axioms CommonRoleClosedIntervalInspection.reconcile_exact
#print axioms CommonRoleIntervalReadyChain.no_readiness_rank
end Cycle74BoundaryCheck
```

出力全文:

```text
'Yulang.CommonRoleIntervalCapture.capture_arguments_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalCandidates.scan_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalCandidates.accepted_child_decreases' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalExpansion.run_tree_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalDictionaries.elaborate_prepared_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalDictionaries.Dictionary.erase_unique' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalDictionaryCompilation.compile_trace_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalCandidateFrontier.solutions_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleIntervalGeneration.generate_real_argument_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleClosedIntervalRecordGeneration.compile_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleClosedIntervalInspection.reconcile_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleIntervalReadyChain.no_readiness_rank' depends on axioms: [propext, Quot.sound]
```

公理確認対象の読み方（すべて既存定理）:
- capture_arguments_exact / scan_exact: 任意有限head/endpoint/bindingまたはregistry/goal/candidate列について、実行のsome iff独立capture/selection。断片の健全性・完全性の補助。
- accepted_child_decreases: 任意declaration/goal/bindings/元whereについて、実checker成功・Accepts・所属の前提から両端点サイズ和が減少。停止補助。
- run_tree_exact: 任意有限registry/goal/treeで、実runがtreeを返す iff Checkedと独立Traversal。構造断片の健全性・完全性。
- elaborate_prepared_exact: 任意registry/goal/plan/traceでprepared iff Checkedと、同じerase/traceを持つ独立Dictionaryの存在。ordinary解決成功ではない。
- Dictionary.erase_unique: 同じregistry/goalの任意二辞書のeraseが等しい。補助。別source順の一般辞書同値ではない。
- compile_trace_exact: 任意name map/original atoms/assignment/traceで、元制約とtrace整合 iff literal readbackを持つcompiled graphモデルの存在。生成の健全性・完全性。
- solutions_exact: 任意State/二slot request/scalar候補/assignmentについて、元stateと二端点条件 iff全ordinary solution familyのあるinstanceとassignmentが同値。局所の健全性・完全性・全instance表現、M1全体の主型性ではない。
- generate_real_argument_exact: 任意interval列/assignmentで全生成atoms iff全intervalに入る意味論的actualの存在。区間生成の健全性・完全性。
- closed compile_exact: 任意有限existing/labels/fields/request/assignmentで元制約とCompatible iff literal readbackを持つgraphモデルの存在。閉record断片の生成の健全性・完全性。
- reconcile_exact: 任意assignment/二field列で、返ったatomsを満たす iff SameLabelsと四つのCompatible条件。閉record断片の健全性・完全性。
- no_readiness_rank: 固定の無限familyについて全隣接段階で減少する自然数rankは存在しない。補助反例。growing宣言はcheckerに拒否される。

### inventory・差分

`python tools/boundary-input-inventory.py`、`python tools/boundary-input-inventory.py --check`
はexit0。出力:

```text
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=242; Main=93; Audit=242; ledger mentioned=99. Mention counts are not audit completion counts.
```

TSV列数/一意性/件数、K節16moduleと全相対リンクの存在も確認した:

```text
PASS: 16 K-section module rows exist; ledger relative links resolve; 242 unique 7-column inventory rows; mentions=99 (not completed audits).
```

`git diff --check` exit0、`git diff --quiet c4043b524 -- lean` exit0。
`bash tools/verify-lean.sh . origin/integration/m1-final --no-build` exit0。出力全文:

```text
verify-lean: . @ 9652c1b6e (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

これはdiff-only検査。**全体lake build、全Audit/AxiomGate、build付きverify-leanは未実行。**
公開後の全体検証は監督役に残る。未公開commitに対するremote CI成功は主張しない。

## 公開ブロッカーと保持ファイル

Git object作成による`momota1029/yulang`の`work/dots-main`への公開は前cycle以来
審査拒否・新しい許可待ち。今回のremote書込は0回。blob/tree/commit/ref作成、push、
同等の別経路を再試行していない。開始/終了心拍もlocalのみで、外部から見える心拍ではない。

integrationからの未公開差分は本報告を含め18path:
- `lean/Audit.lean`
- `lean/README.md`
- `lean/Yulang.lean`
- `lean/Yulang/CommonRoleAddressedCaptureModels.lean`
- `notes/design/2026-11-10-boundary-input-coverage.tsv`
- `notes/design/2026-11-10-boundary-inputs-ledger.md`
- `notes/design/2026-11-10-cycle69-addressed-capture-models.md`
- `notes/design/INDEX.md`
- `notes/handoff/dots-cycle-69.md`
- `notes/handoff/dots-cycle-70.md`
- `notes/handoff/dots-cycle-71.md`
- `notes/handoff/dots-cycle-73.md`
- `notes/handoff/dots-cycle-74.md`
- `notes/heartbeat/dots-main-crash-72.md`
- `notes/heartbeat/dots-main.md`
- `notes/questions/2026-11-10-cycle70-associated-sugar-checking.md`
- `notes/questions/2026-11-10-cycle70-invocation-sharing-boundary.md`
- `tools/boundary-input-inventory.py`

新たな許可が来るまで拒否された公開操作を再試行しない。許可後に最新integrationと
API live workを再取得し、対象外pathを保つnon-force・expected-headの一括公開と
公開tree/blobの照合が必要。既存未公開commitを捨てずに再開する。

## Yulang2との照合と次の候補

既存`notes/audit/y2-claims-role-boundaries-cycle-2.md` ROLE-MORE-001〜005と
`x-oracle.md` X13〜X16/C3-PARENTを再読した。旧whereが効かない例を新specへ採用しない。
X13〜X16は局所sourceのCLI観測で、任意intervalや内部交差条件の完全なoracleではない。
新しいYulang2実行、parser実行はしていない。

残るB4主要橋は5本:
`source_boundary_adequate`、`generated_work_closed`、`saturate_terminates_and_closes`、
`saturated_frontier_exact`、`resolve_dictionary_order_sound`。

次の監査候補:
1. 一般ordinary state→graph readout/adapterのadequacy前提と、K節の実compiled graphの区別。
2. Mainに再掲されるassociated/where exactnessの全入力と台帳の対応。
3. 残るCommonRole moduleをinventoryで特定し、旧点モデル/反例/実入口の入力を分ける。

## 時間と資源

報告保存: 2026-11-10T08:08:01Z。起動予定から11.0分、25分以内。
開始と終了の空きは48G/63G、使用13G。作業場とcacheは一つのまま。
時間を埋めるためのproduction補題は追加していない。使用量枠は不明。
