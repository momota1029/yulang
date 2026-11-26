# C441 — immutable source 検証と実入口テスト

## Exact build / audit

- 開始時正本 `integration/m1-final@2e47eb95797eda5d68d1b62ac1664fe07cb1d2c5`（Lean `5d57993d91ace99c523aaca4b6d8804d4b1498aa`、C440 exact 採用）。作業入力 `52b81062a3c9deb7e95494a43aff696bda1ee423`。仕様と inbox の読み取りは正本側（work の旧 spec が正本と同じだとはしない）。spec/ や古い説明の変更なし。
- 科学 pin `658106bae52323f830bec55a8ee3349b2815774e`、Lean tree `f9471c73c28ed615317a4de8ff847af8b093e97d`。13 Git source blobs が staging bytes と完全一致。`git hash-object --stdin` の再計算と人手別プロセスの独立役で照合。使った既存 import closure 4,083 / 4,083 の source provenance は正本と一致。既存 production 7,682 / independent Audit 2,069 同一。barrel の元の 375,968 bytes を保ち、6 imports を追加。凍結ファイル二つは本文未読、Git blob IDs のみ同一確認。
- 公式 Lean 4.35.0 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。6 production を各 `-o`、7 Audit は各別 clean directory + production-only oleans + Audit oleans なしで再実行。全部終了コード 0、warning なし。47 independent audit の公理は `propext`、`Classical.choice`、`Quot.sound` の部分集合のみ。
- Audit の import: `Yulang.*` 以外 0 件。全 `lake build`、全 `tools/verify-lean.sh` または Rust 版の実行は今回の dot ではしない。

```sh
LEAN_PATH=<production-only olean root> lean --trust=0 -DwarningAsError=true -o <root>/Yulang/<module>.olean <production source>
LEAN_PATH=<same production-only olean root> lean --trust=0 -DwarningAsError=true <single standalone Audit source>
```

| immutable path | Git blob | Audit 宣言数 |
| --- | --- | ---: |
| `lean/Yulang/GeneralDeclarativeI65I74RefPositionSource441.lean` | `083dc2485692a91fca30b2741dbb824c31d64843` | — |
| `lean/Audit/Cycle441I74RefPositionSource.lean` | `49cd5ca78762b95debe89a0e4bda28cee3569ec0` | 7 |
| `lean/Yulang/GeneralDeclarativeI65I74RefPositionRead441.lean` | `4601953678018259799ee97139ae7bc3eb666fb2` | — |
| `lean/Audit/Cycle441I74RefPositionRead.lean` | `9c1ad685f38ba00d1b589c68ef043cf2adaecfc5` | 2 |
| `lean/Yulang/GeneralDeclarativeI65I74RefPositionRule441.lean` | `83a6d2a0fdf55fdc4e6a044b5473d6fa80150448` | — |
| `lean/Audit/Cycle441I74RefPositionRule.lean` | `77a605f83376835d7ce408d732b09b279346e0ab` | 6 |
| `lean/Yulang/GeneralDeclarativeI65I74RefPositionEntry441.lean` | `b6a53d10cbf32bcc8c7e6c2d5f4bcb7cbf33f558` | — |
| `lean/Audit/Cycle441I74RefPositionEntry.lean` | `02494eed502b20c2d520b58adb2675dd3c7b962e` | 8 |
| `lean/Audit/Cycle441I74RefPositionEndToEnd.lean` | `6dc6f0325d25c29ff1f1ffc4db012d32005245d0` | 7 |
| `lean/Yulang/GeneralDeclarativeI65I74RefPositionBoundary441.lean` | `852acc79fb59aef64a6d78fed33d4b901d7acad3` | — |
| `lean/Audit/Cycle441I74RefPositionBoundary.lean` | `83df3654e1f5f43c19a8efe974fc71829396609e` | 12 |
| `lean/Yulang/GeneralDeclarativeI65I74RefPositionFidelity441.lean` | `9e7c365d2cbdeaea49f6efca61de49f341850fcd` | — |
| `lean/Audit/Cycle441I74RefPositionFidelity.lean` | `f93f3ab2253deb47a739af4a8a123a99dc5685bf` | 5 |

## 実入口と対照

`R21.check` の順で、実二 binder (true)、mode 順交換、endpoint 順交換、同じ binder の使い回し、実 rival、issuer 違い、report 違い、literal Problem の構成可否 (true)、literal 当該分岐、raw root cycle 当該分岐、実 raw root K2 従来分岐 (true)：

```text
[true, false, false, false, false, false, false, true, false, false, true]
```

- §4.6 `run` で field-local `'f` を公開 header に入れない投影。公開 row/value それぞれが owner の同じ root 0 からたどれる場合も、実 program で covariant row と invariant value、実 R21 true、実 signed row の適合モデルと元の dictionary evidence まで別に確認。field-local forall を実装したとはしない。
- 元の literal `ref _ int` の signed row + ordinary Int 用に、実 catalogue と二 channel を持つ concrete Problem を組み立てる。適合モデルがあって既存の forward comparison は成立するのに、元の fixed named `SourceHead` が構成できず、今周の scoped binder 分岐は false。§6.2 の言語拒否と混同しない。
- さらに scalar Int 葉**だけ**なら、元の declaration metadata `readUse` / Primitive と旧 `translate` は本物の `.primitive (.scalar .int) []` を導出し、任意の assignment で Int になる。足りないのは、それを元の typed mixed head 内の ordinary literal endpoint に結びつける fixed evidence で、Int 名の推測や type-table の欠落ではない。
- 独立の元 root 値が普通の Bool でも typed original syntax/row/value capture の fitting interpretation が可能な例では、実入口は同じ。旧 ordinary root の whole-value equality の証拠を新たに推定していない。逆に raw model が実 mixed nominal を表す場合、それを all-value legacy encoder と同値にすることは不可能（本体の一般定理）。
- 別 binder が同じ物理数値 slot に格納された row/value の二成分を読む case も、signed effect と Int の両方を保って actual checker true。それぞれ別 binder という syntax 要件と、物理名が同じということは別。
- value binder の下の real raw regular cycle `µ = :{8 µ}` は実際に循環上にあるが、そこは候補 head が見る位置ではない。新入口 true、同じ model で signed row、µ と実辞書あり。一方 source argument root の raw cycle は旧入口の actual K2 rejection を優先する。
- C440 の実 three-mode fixtures（非点内側 interval、二つの適合モデル）も一段外の R21 prior witness を通ってそのまま。同じ証拠の旧分岐を使い、C440 の条件は広げない。

## 公開 Audit の完全 axioms 出力

```text
lean/Audit/Cycle441I74RefPositionSource.lean exit 0
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.two_bindings_visit_only_root441' depends on axioms: [propext]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.Original.rowCapture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.Original.valueCapture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.Original.compare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.Original.head' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.actual_typed_positions_mean_in_same_model441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.no_raw_cycle_at_either_binder441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

lean/Audit/Cycle441I74RefPositionRead.lean exit 0
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.replay441' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.read_checks_own_row_and_value_in_order441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

lean/Audit/Cycle441I74RefPositionRule.lean exit 0
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.Original.picked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.Original.actualOrigin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.Local.evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.ref_only_dictionary_sound441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.actual_ref_selected_trace441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.actual_ref_classifies441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

lean/Audit/Cycle441I74RefPositionEntry.lean exit 0
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.dictionary_sound_R21' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.all_previous_R20_Bool_unchanged441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.checked_ref_returns_original_report441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.check_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.verified_R21_result_classifies_in_same_State441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.checked_ref_retains_raw_priority441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.no_new_ref_selection_over_original_raw_root441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.original_raw_root_is_first_in_R21441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

lean/Audit/Cycle441I74RefPositionEndToEnd.lean exit 0
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.ScopedExample.actual_run_projection_derives_ordered_modes441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.ScopedExample.actual_public_ref_role_check441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.ScopedExample.wrong_mode_order_wrong_endpoint_order_same_binder_and_rival_do_not_use_new_branch441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.ScopedExample.literal_source_problem_is_real_but_not_the_two_binder_lane441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.ScopedExample.actual_unfiltered_raw_root_precedes_new_scope441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.ScopedExample.actual_ref_with_signed_effect_fits441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.ScopedExample.exact_mixed_ref_dictionary_and_effect_not_value_slot441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

lean/Audit/Cycle441I74RefPositionBoundary.lean exit 0
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.Boundary.source_positions_forward' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.Boundary.wrong_position_has_no_comparison' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.Boundary.no_deep_literal_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.Boundary.no_deep_rigid_int_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.Boundary.centered_compiler_cannot_translate_row_value_app' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.Boundary.row_value_deep_replay_cannot_consume_rigid_int' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.Boundary.fixed_ordered_head_for_rigid_ref_has_no_current_constructor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.Boundary.fixed_named_source_head_replay_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.Boundary.both_typed_positions_inherited' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.Boundary.forward_row_is_not_reverse' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.Boundary.every_accepted_source_use_has_original_formal_positions441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.Boundary.typed_ref_forward_context_distinguishes_signed_rows441' depends on axioms: [propext,
 Quot.sound]

lean/Audit/Cycle441I74RefPositionFidelity.lean exit 0
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.same_visible_ref_occurrence441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.same_fitting_ref_names441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.two_verified_ref_wires_preserve_each_original_channel441' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.typed_ref_cannot_be_flattened_to_legacy_value_arguments441' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDeclarativeI65.I72.RefPositions441.legacy_raw_encoder_has_no_mixed_row_value_image441' depends on axioms: [propext,
 Quot.sound]
```

## 独立 QA の再現（上の公開 47 とは別）

次の名前空間はそれぞれ独立に Git pin の `lean/Audit/Cycle441I74RefPositionEndToEnd.lean` と **一つの** source にし、同じ production-only import 環境で `lean --trust=0 -DwarningAsError=true --stdin`。Audit 間の import はしない。literal fixture は先頭に `import Yulang.GeneralDeclarativeI65I74RefPositionBoundary441` を加える。isolated scalar leaf は先頭の import を含み単独。旧 C440 prior test は正本の `lean/Audit/Cycle440I74NestedInvariantEndToEnd.lean` を元に、その先頭に `import Yulang.GeneralDeclarativeI65I74RefPositionEntry441` を加えた単一 source。すべて strict exit 0。

### Runtime
```lean
open Yulang.GeneralDeclarativeI65.I72.RefPositions441
open Yulang.GeneralDeclarativeI65.I72.RefPositions441.ScopedExample
open Yulang.GeneralDeclarativeI65 in
#eval [test,
  test (build [actual] crossed),
  test (build [actual] registry [⟨0,[71],.nominal 9 [valueArg 2,rowArg 1]⟩]),
  test (build [reusedBinder]),
  test (build [actual,rival]),
  test (build [actual] registry [⟨0,[77],authoredEndpoint⟩]),
  test build {chosen with tree := .ambiguous},
  literalProblem.isSome,
  test literalProblem (leafReport literal),
  test (build [actual] registry [witnessOrigin] rawCycle),
  test (build [actual] registry [witnessOrigin] rawCycle) Yulang.GeneralDeclarativeI65.I72.Check408.rawReport previousRoot]
```

### Whole projected owner / actual variance and same model
```lean
namespace Yulang.GeneralDeclarativeI65.I72.RefPositions441.WholeRunQA
open GeneralDeclarativeI65
open Yulang.GeneralDeclarativeI65.I72.RefPositions441.ScopedExample
open GeneralDeclarativeWitnessSparseVariance357 (Source Made compile lookup)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open Checker408 (Problem)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (subtype_refl)

def wholeRunProjection : Source 3 1 1 := {authoredRunProjection with roots := fun _ => 0}

def fromWholeRun : Option Problem := do
  let graph ← compile wholeRunProjection
  let book ← GeneralSourceMetadataBareBundle291.compile (surface [actual])
  let env : Environment := ⟨3,1,1,wholeRunProjection,graph,book⟩
  let s : GeneralDeclarativeI65.State := ⟨⟨env,ordinary,[]⟩,registry,[witnessOrigin],[]⟩
  let b6 : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,b6⟩,⟨[71],roleDemand⟩⟩

theorem actual_complete_projected_run_modes441 :
    ((compile wholeRunProjection).bind fun made => lookup made 9) = some layout := by decide +kernel

theorem both_formals_in_full_projected_owner_body441 :
    ∃ made : Made wholeRunProjection, compile wholeRunProjection = some made ∧
      CommonDeclarationVarianceTable.Mode made.program 1 .covariant ∧
      CommonDeclarationVarianceTable.Mode made.program 0 .invariant := by
  obtain ⟨made,read,atMode⟩ := Option.bind_eq_some_iff.mp actual_complete_projected_run_modes441
  have body := GeneralDeclarativeWitnessVariancePositions357.authored_modes_exact made atMode
  obtain ⟨h,source,_,ordered⟩ := body
  have same := List.mem_singleton.mp source
  subst h
  refine ⟨made,read,?_⟩
  cases ordered with
  | cons row tail =>
    cases tail with
    | cons value _ => exact ⟨row.2,value.2⟩

theorem actual_ref_public_check_uses_both_owner_roots441 :
    test fromWholeRun = true := by decide +kernel

theorem whole_run_keeps_original_fitting_signed_model441 {p : Problem}
    (probe : fromWholeRun = some p) : I72.Fits p.state model := by
  unfold fromWholeRun at probe
  cases graph : compile wholeRunProjection with
  | none => simp [graph] at probe
  | some cooked =>
    cases book : GeneralSourceMetadataBareBundle291.compile (surface [actual]) with
    | none => simp [graph,book] at probe
    | some actualBook =>
      simp only [graph,book,Option.pure_def] at probe
      cases probe
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro a used
        change a ∈ [rowOne,valTwo] at used
        simp only [List.mem_cons,List.not_mem_nil,or_false] at used
        rcases used with rfl|rfl
        · exact Common.rowLe_refl _
        · exact subtype_refl _
      · intro _ nil; cases nil
      · intro e seen
        change e ∈ [intRow] at seen
        cases List.mem_singleton.mp seen
        exact eqv_refl _
      · intro _ nil; cases nil
      · intro o seen
        change o ∈ [witnessOrigin] at seen
        cases List.mem_singleton.mp seen
        rfl

theorem whole_owner_run_projection_uses_actual_entry_and_fixed_evidence441 :
    ∃ p, fromWholeRun = some p ∧ I72.Fits p.state model ∧
      check p chosen (.reference wire) = true ∧ ReportEvidence p.state model p.root chosen := by
  have yes := actual_ref_public_check_uses_both_owner_roots441
  cases found : fromWholeRun with
  | none => simp [test,found] at yes
  | some p =>
    have good : check p chosen (.reference wire) = true := by simpa [test,found] using yes
    have fitting := whole_run_keeps_original_fitting_signed_model441 found
    exact ⟨p,rfl,fitting,good,(check_sound p _ _ good).2 _ fitting⟩

#print axioms actual_complete_projected_run_modes441
#print axioms both_formals_in_full_projected_owner_body441
#print axioms actual_ref_public_check_uses_both_owner_roots441
#print axioms whole_run_keeps_original_fitting_signed_model441
#print axioms whole_owner_run_projection_uses_actual_entry_and_fixed_evidence441
end Yulang.GeneralDeclarativeI65.I72.RefPositions441.WholeRunQA
```

### Literal actual negative carrier case
```lean
namespace Yulang.GeneralDeclarativeI65.I72.RefPositions441.LiteralFixtureQA
open GeneralDeclarativeI65
open Yulang.GeneralDeclarativeI65.I72.RefPositions441.ScopedExample
open GeneralDeclarativeI65.I72.RefPositions441.Boundary
open GeneralDeclarativeWitnessSparseVariance357 (compile)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Constructor)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)
open CommonNominalFullCarrier (subtype_refl)
open Checker408 (Problem)

def literalModel : I72.Model :=
  {model with nativeSyntax := fun n => if n = 0 then some exactLiteralEndpoint else none}

def literalRef : Constructor := ⟨[.row,.type],9⟩

theorem existing_actual_literal_kind441 {p : Problem} (h : literalProblem = some p) :
    (authoredRegistry p.state.core.current).constructors 9 = some literalRef := by
  have actual : (literalProblem.map fun p => (authoredRegistry p.state.core.current).constructors 9) =
      some (some literalRef) := by decide +kernel
  rw [h] at actual
  exact Option.some.inj actual

theorem original_literal_fits_and_reads_its_route441 {p : Problem} (h : literalProblem = some p) :
    I72.Fits p.state literalModel ∧
      p.root.demand.arguments = [⟨0,0,0⟩] ∧
      p.state.core.modes[9]? = some layout ∧
      (⟨0,[71],exactLiteralEndpoint⟩ : Origin) ∈ p.state.core.origins ∧
      ∀ o ∈ p.state.core.origins, o.endpoint = exactLiteralEndpoint := by
  unfold literalProblem build at h
  cases graph : compile authoredRunProjection with
  | none => simp [graph] at h
  | some sem =>
    cases book : GeneralSourceMetadataBareBundle291.compile (surface [literal]) with
    | none => simp [graph,book] at h
    | some src =>
      simp only [graph,book,Option.pure_def] at h
      cases h
      refine ⟨?_,rfl,rfl,List.mem_cons_self,?_⟩
      · refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
        · intro a used
          change a ∈ [rowOne,valTwo] at used
          simp only [List.mem_cons,List.not_mem_nil,or_false] at used
          rcases used with rfl|rfl
          · exact Common.rowLe_refl _
          · exact subtype_refl _
        · intro _ bad; cases bad
        · intro e used
          change e ∈ [intRow] at used
          cases List.mem_singleton.mp used
          exact eqv_refl _
        · intro _ bad; cases bad
        · intro o used
          change o ∈ [⟨0,[71],exactLiteralEndpoint⟩] at used
          cases List.mem_singleton.mp used
          rfl
      · intro o used
        change o ∈ [⟨0,[71],exactLiteralEndpoint⟩] at used
        cases List.mem_singleton.mp used
        rfl

theorem real_typed_literal_is_comparable_in_its_fitting_model441 :
    ∃ p, literalProblem = some p ∧
      I72.Fits p.state literalModel ∧
      ContextDerives p.state.core.modes literalModel.assignment false exactLiteralEndpoint exactLiteralEndpoint ∧
      ¬Nonempty (SourceHead p.state.core p.root literal) ∧
      check p (leafReport literal) (.reference wire) = false := by
  have existsP := literal_source_problem_is_real_but_not_the_two_binder_lane441.1
  cases h : literalProblem with
  | none => simp [h] at existsP
  | some p =>
    obtain ⟨fitting,arg,modes,_,same⟩ := original_literal_fits_and_reads_its_route441 h
    have okay : ContextDerives p.state.core.modes literalModel.assignment false
        exactLiteralEndpoint exactLiteralEndpoint :=
      .nominal modes (.cons (.covariantRow (Common.rowLe_refl _)) (.cons
        (.invariantValue (.ordinary (subtype_refl _)) (.ordinary (subtype_refl _))
          (.ordinary (subtype_refl _)) (.ordinary (subtype_refl _))) (.nil false)))
    have typed := fixed_named_source_head_replay_gap (d := literal) (ref := 9) (binder := 6) (int := 20)
      arg rfl (show literalRef.parameters = [.row,.type] from rfl)
      (existing_actual_literal_kind441 h) modes
      (fun o used _ => ⟨.var 1,same o used⟩)
    have no := literal_source_problem_is_real_but_not_the_two_binder_lane441.2
    exact ⟨p,rfl,fitting,okay,typed,by simpa [test,h] using no⟩

#print axioms existing_actual_literal_kind441
#print axioms original_literal_fits_and_reads_its_route441
#print axioms real_typed_literal_is_comparable_in_its_fitting_model441
end Yulang.GeneralDeclarativeI65.I72.RefPositions441.LiteralFixtureQA
```

### Authored scalar leaf is available on its own
```lean
import Yulang.GeneralDeclarativeI65I74RefPositionBoundary441

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RefPositions441.IntLeafQA
open GeneralDeclarativeI65
open GeneralDeclarativeWitnessConstructorModes357 (Use SourceMode)
open GeneralDeclarativeWitnessDeclaredState357 (Current authoredRegistry)
open GeneralNominalCenteredHeadMatExpressions (translate translateMany application value)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarationPatterns (Pattern)
open CommonNominalFullCarrier (Ty)
open GeneralNominalMaterialization (Mode)

/-- The primitive leaf needed by the literal fixture is already an actual
  authorised, typeable leaf in isolation. No predicate on the final
  classification/assignment and no operand slot substitution is assumed. -/
theorem independent_authored_int_leaf_has_exact_old_translation441 {c : Current}
    {intKey : Nat} (u : Use c.environment intKey 0)
    (asInt : u.mode = .primitive (.scalar .int)) :
    translate (authoredRegistry c).constructors (interpretation c.environment.source.snapshot)
      (.app intKey []) = some (.primitive (.scalar .int) []) := by
  have source : SourceMode c.environment intKey (.primitive (.scalar .int)) := asInt ▸ u.sourced
  have op : (interpretation c.environment.source.snapshot).primitives intKey = some (.scalar .int) := by
    cases source with
    | primitive actual _ => exact actual
  have found : (authoredRegistry c).constructors intKey = some u.declared := u.actual
  have noParameters : u.declared.parameters = [] :=
    List.length_eq_zero_iff.mp u.exactArity
  simp [translate,translateMany,application,found,noParameters,op,
    GeneralCandidateInspection.Primitive.parameters]

theorem translated_leaf_means_Int_for_every_assignment441
    {c : Current} {intKey : Nat} (u : Use c.environment intKey 0)
    (asInt : u.mode = .primitive (.scalar .int)) :
    ∀ variables : Mode → Nat → Ty, ∀ mode,
      (translate (authoredRegistry c).constructors (interpretation c.environment.source.snapshot)
        (.app intKey [])).map (value variables mode) = some (.base .int) := by
  intro vars mode
  rw [independent_authored_int_leaf_has_exact_old_translation441 u asInt]
  rfl

#print axioms independent_authored_int_leaf_has_exact_old_translation441
#print axioms translated_leaf_means_Int_for_every_assignment441
end Yulang.GeneralDeclarativeI65.I72.RefPositions441.IntLeafQA
```

### Separate physical and typed roots
```lean
namespace Yulang.GeneralDeclarativeI65.I72.RefPositions441.RawSeparationQA
open GeneralDeclarativeI65
open Yulang.GeneralDeclarativeI65.I72.RefPositions441.ScopedExample
open GeneralDeclarativeWitnessSparseVariance357 (compile)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (Equivalent nominal subtype_refl)
open CommonNominalFullDemand (Environment producerLe_iff_probe)
open Checker408 (Problem)

def otherRawModel : I72.Model :=
  {model with assignment := fun n => if n = 0 then (.base .bool,Common.rowEmpty) else model.assignment n}

theorem separate_native_origin_does_not_assign_legacy_root_value441 {p : Problem} (h : build = some p) :
    I72.Fits p.state otherRawModel := by
  unfold build at h
  cases graph : compile authoredRunProjection with
  | none => simp [graph] at h
  | some sem =>
    cases book : GeneralSourceMetadataBareBundle291.compile (surface [actual]) with
    | none => simp [graph,book] at h
    | some src =>
      simp only [graph,book,Option.pure_def] at h
      cases h
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro a member
        change a ∈ [rowOne,valTwo] at member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl
        · exact Common.rowLe_refl _
        · exact subtype_refl _
      · intro _ bad; cases bad
      · intro e seen
        change e ∈ [intRow] at seen
        cases List.mem_singleton.mp seen
        exact eqv_refl _
      · intro _ bad; cases bad
      · intro o read
        change o ∈ [witnessOrigin] at read
        cases List.mem_singleton.mp read
        rfl

theorem ordinary_root_is_not_the_new_typed_ref_meaning441 :
    ¬Equivalent (otherRawModel.assignment 0).1 (nominal 9 [.inr effect,.inl (.base .int)]) := by
  intro eqv
  let env : Environment Common.Row := ⟨fun _ => .bottom,fun _ => []⟩
  have wrong := (producerLe_iff_probe _ _).mp (eqv.1 0) 0 env (.nominalHead 9 2)
    (by exact ⟨rfl,rfl⟩)
  exact wrong

theorem actual_typed_rule_stays_separate_from_ordinary_root_equivalence441 :
    ∃ p, build = some p ∧ check p chosen (.reference wire) = true ∧
      I72.Fits p.state otherRawModel ∧
      ReportEvidence p.state otherRawModel p.root chosen ∧
      ¬Equivalent (otherRawModel.assignment 0).1 (nominal 9 [.inr effect,.inl (.base .int)]) := by
  have yes := actual_public_ref_role_check441
  cases src : build with
  | none => simp [test,src] at yes
  | some p =>
    have ok : check p chosen (.reference wire) = true := by simpa [test,src] using yes
    have fit := separate_native_origin_does_not_assign_legacy_root_value441 src
    exact ⟨p,rfl,ok,fit,(check_sound p _ _ ok).2 _ fit,ordinary_root_is_not_the_new_typed_ref_meaning441⟩

#print axioms separate_native_origin_does_not_assign_legacy_root_value441
#print axioms ordinary_root_is_not_the_new_typed_ref_meaning441
#print axioms actual_typed_rule_stays_separate_from_ordinary_root_equivalence441
end Yulang.GeneralDeclarativeI65.I72.RefPositions441.RawSeparationQA
```

### Same numeric source slot, both genuine kinds
```lean
namespace Yulang.GeneralDeclarativeI65.I72.RefPositions441.SharedSlotQA
open GeneralDeclarativeI65
open Yulang.GeneralDeclarativeI65.I72.RefPositions441.ScopedExample
open GeneralDeclarativeWitnessSparseVariance357 (compile)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (nominal subtype_refl)
open GeneralDeclarativeHead320 (Equation)
open PresenceNormalForm (Atom)
open Checker408 (Problem)

def sharedOrigin : Origin := ⟨0,[71],endpoint 9 1 1⟩
def valueOne : Atom Nat := .tyLe (.var 1) (.var 1)
def scalarOne : Equation := ⟨1,.primitive (.scalar .int) []⟩
def sharedRaw : GeneralDeclarativeHead320.State := ⟨⟨[rowOne,valueOne],[]⟩,[scalarOne]⟩

def sharedProblem : Option Problem := build [actual] registry [sharedOrigin] sharedRaw

theorem distinct_binders_may_read_two_channels_of_one_actual_slot441 :
    test sharedProblem = true := by decide +kernel

def sharedModel : I72.Model :=
  ⟨fun n => match n with
    | 0 => (nominal 9 [.inr effect,.inl (.base .int)],Common.rowEmpty)
    | 1 => (.base .int,effect)
    | _ => (.bottom,Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some sharedOrigin.endpoint else none⟩

theorem signed_row_and_int_coexist_at_same_original_model_slot441 {p : Problem}
    (got : sharedProblem = some p) : I72.Fits p.state sharedModel := by
  unfold sharedProblem build at got
  cases graph : compile authoredRunProjection with
  | none => simp [graph] at got
  | some sem =>
    cases book : GeneralSourceMetadataBareBundle291.compile (surface [actual]) with
    | none => simp [graph,book] at got
    | some src =>
      simp only [graph,book,Option.pure_def] at got
      cases got
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro a member
        change a ∈ [rowOne,valueOne] at member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl
        · exact Common.rowLe_refl _
        · exact subtype_refl _
      · intro _ bad; cases bad
      · intro e member
        change e ∈ [scalarOne] at member
        cases List.mem_singleton.mp member
        exact eqv_refl _
      · intro _ bad; cases bad
      · intro o on
        change o ∈ [sharedOrigin] at on
        cases List.mem_singleton.mp on
        rfl

theorem same_address_with_different_kinds_is_not_binder_confusion441 :
    ∃ p, sharedProblem = some p ∧ check p chosen (.reference wire) = true ∧
      I72.Fits p.state sharedModel ∧ ReportEvidence p.state sharedModel p.root chosen ∧
      (sharedModel.assignment 1).1 = .base .int ∧ (sharedModel.assignment 1).2 (56,[1,-2]) := by
  have yes := distinct_binders_may_read_two_channels_of_one_actual_slot441
  cases found : sharedProblem with
  | none => simp [test,found] at yes
  | some p =>
    have accepted : check p chosen (.reference wire) = true := by simpa [test,found] using yes
    have fit := signed_row_and_int_coexist_at_same_original_model_slot441 found
    exact ⟨p,rfl,accepted,fit,(check_sound p _ _ accepted).2 _ fit,rfl,rfl⟩

#print axioms distinct_binders_may_read_two_channels_of_one_actual_slot441
#print axioms signed_row_and_int_coexist_at_same_original_model_slot441
#print axioms same_address_with_different_kinds_is_not_binder_confusion441
end Yulang.GeneralDeclarativeI65.I72.RefPositions441.SharedSlotQA
```

### Real uninspected cyclic value binder
```lean
namespace Yulang.GeneralDeclarativeI65.I72.RefPositions441.OffPathQA
open GeneralDeclarativeI65
open Yulang.GeneralDeclarativeI65.I72.RefPositions441.ScopedExample
open GeneralDeclarativeWitnessSparseVariance357 (compile)
open GeneralDeclarativeHead320 (Equation)
open CommonNominalFullCarrier (Ty Equivalent nominal variant subtype_refl)
open Checker408 (Problem)

def mu : Ty := .variant 8 (.block [.variant 8 (.inl 0)] 0)

theorem actual_mu_eq_its_unfolding441 : Equivalent mu (variant 8 mu) := by
  have same (depth : Nat) : CommonNominalFullCarrier.observeTy depth mu =
      CommonNominalFullCarrier.observeTy depth (variant 8 mu) := by cases depth <;> rfl
  constructor
  · intro depth; rw [←same depth]; exact CommonNominalFullDemand.producerLe_refl _
  · intro depth; rw [←same depth]; exact CommonNominalFullDemand.producerLe_refl _

def leafRow : Equation := ⟨2,.variant 8 (.variable 2)⟩
def raw : GeneralDeclarativeHead320.State := {ordinary with equations := [leafRow]}
def leafLoop : GeneralDeclarativeWitnessCycle350.Wire := ⟨0,⟨0,.same,2⟩,[],.same⟩
def request := (GeneralDeclarativeDemand320.Demand.mk 7 [⟨2,2,2⟩] [])

theorem typed_value_binder_contains_genuine_off_path_cycle441 :
    GeneralDeclarativePriority321.RootRecurs raw request ∧
    test (build [actual] registry [witnessOrigin] raw) = true :=
  ⟨GeneralDeclarativeWitnessCycle350.rooted (w := leafLoop) (by decide +kernel),by decide +kernel⟩

def actualFit : I72.Model :=
  {model with assignment := fun n => match n with
    | 0 => (nominal 9 [.inr effect,.inl mu],Common.rowEmpty)
    | 2 => (mu,Common.rowEmpty)
    | _ => model.assignment n}

theorem same_model_works_for_uninspected_real_cycle441 {p : Problem}
    (got : build [actual] registry [witnessOrigin] raw = some p) : I72.Fits p.state actualFit := by
  unfold build at got
  cases graph : compile authoredRunProjection with
  | none => simp [graph] at got
  | some sem =>
    cases book : GeneralSourceMetadataBareBundle291.compile (surface [actual]) with
    | none => simp [graph,book] at got
    | some src =>
      simp only [graph,book,Option.pure_def] at got
      cases got
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro a found
        change a ∈ [rowOne,valTwo] at found
        simp only [List.mem_cons,List.not_mem_nil,or_false] at found
        rcases found with rfl|rfl
        · exact Common.rowLe_refl _
        · exact subtype_refl _
      · intro _ bad; cases bad
      · intro row found
        change row ∈ [leafRow] at found
        cases List.mem_singleton.mp found
        exact actual_mu_eq_its_unfolding441
      · intro _ bad; cases bad
      · intro o found
        change o ∈ [witnessOrigin] at found
        cases List.mem_singleton.mp found
        rfl

theorem solver_scope_keeps_its_original_signed_row_with_cyclic_captured_value441 :
    ∃ p, build [actual] registry [witnessOrigin] raw = some p ∧
      check p chosen (.reference wire) = true ∧ I72.Fits p.state actualFit ∧
      ReportEvidence p.state actualFit p.root chosen ∧
      (actualFit.assignment 1).2 (56,[1,-2]) := by
  have yes := typed_value_binder_contains_genuine_off_path_cycle441.2
  cases found : build [actual] registry [witnessOrigin] raw with
  | none => simp [test,found] at yes
  | some p =>
    have ok : check p chosen (.reference wire) = true := by simpa [test,found] using yes
    have fit := same_model_works_for_uninspected_real_cycle441 found
    exact ⟨p,rfl,ok,fit,(check_sound p _ _ ok).2 _ fit,rfl⟩

#print axioms actual_mu_eq_its_unfolding441
#print axioms typed_value_binder_contains_genuine_off_path_cycle441
#print axioms same_model_works_for_uninspected_real_cycle441
#print axioms solver_scope_keeps_its_original_signed_row_with_cyclic_captured_value441
end Yulang.GeneralDeclarativeI65.I72.RefPositions441.OffPathQA
```

### Actual C440 earlier witness through the new wrapper
```lean
namespace Yulang.C441PriorEntryQA
open GeneralDeclarativeI65.I72
open GeneralDeclarativeI65.I72.NestedInvariant440.ScopedExample

theorem original_C440_typed_scope_retains_same_R21_report441 (l : Lane) :
    ∃ p, build l = some p ∧
      RefPositions441.check p (report l) (.previous (.nested wire)) = true ∧
        ∀ b, Fits p.state (model l b) ∧
          RefPositions441.ReportEvidence p.state (model l b) p.root (report l) := by
  obtain ⟨p,actual,yes,fit,_⟩ := same_original_nonpoint_selects_fixed_dictionary_with_two_centers440 l
  exact ⟨p,actual,yes,fun b => ⟨(fit b).1,.inl (fit b).2⟩⟩
#print axioms original_C440_typed_scope_retains_same_R21_report441
end Yulang.C441PriorEntryQA
```

### どの local rule でも fixed named lane の literal 選択は出ない

literal fixture の実 scope が実 source compile から得た singleton `[ref _ int]` そのものだと確認。元の typed Problem は同じ適合モデルで valid compare。上の `literal` namespace に下の二つを追加すると、**任意の既存 named `SourcePrimitives` への局所規則追加** だけでは literal 選択が出ない（そこで必要な `Event.head` の証拠が先に不足）。projected/completed や将来の evidence lane について普遍的な不可能性を言っていない。実言語の拒否を導いていない。

```lean
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RefPositions441.NamedGapQA
open GeneralDeclarativeI65
open RefPositions441.Boundary
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Constructor)
open Core.PresenceGeneration (RowTerm)
open CommonRoleOutermostResolver (Dictionary)

/-- A change to an open primitive local rule cannot make an event with
the missing head. This only quantifies over the fixed named SourceTrace,
not other evidence lanes or a future language implementation. -/
theorem no_named_local_rule_can_supply_an_actual_literal_ref_selection441
    {s : I72.State} {q : Request} {d : Declaration} {arg : Capture} {ref binder int : Nat}
    {ctor : Constructor} (single : visible s.core q = [d])
    (asked : q.demand.arguments = [arg]) (literal : d.head = [written ref binder int])
    (layout : ctor.parameters = [.row,.type])
    (catalogue : (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry s.core.current).constructors ref
      = some ctor)
    (table : s.core.modes[ref]? = some modes)
    (routes : ∀ o ∈ s.core.origins, OriginRoute s.core o arg.lower ∨ OriginRoute s.core o arg.upper →
      ∃ e : RowTerm Nat, o.endpoint = .nominal ref (readArgs e)) :
    ∀ (R : SourcePrimitives) (out : Dictionary), ¬Classifies R s q (.selected out) := by
  intro R out chose
  obtain ⟨_,_,⟨trace⟩,summary⟩ := chose
  cases trace with
  | rootK2 => cases summary
  | other status _ _ _ =>
    cases status <;> cases summary
  | selected e _ _ _ _ =>
    have row := e.frame.inScope
    rw [single] at row
    have chosen := List.mem_singleton.mp row
    have head : SourceHead s.core q d := chosen ▸ e.head
    exact fixed_named_source_head_replay_gap asked literal layout catalogue table routes ⟨head⟩

#print axioms no_named_local_rule_can_supply_an_actual_literal_ref_selection441
end Yulang.GeneralDeclarativeI65.I72.RefPositions441.NamedGapQA

namespace Yulang.GeneralDeclarativeI65.I72.RefPositions441.LiteralVisibilityQA
open GeneralDeclarativeI65
open Yulang.GeneralDeclarativeI65.I72.RefPositions441.ScopedExample
open Yulang.GeneralDeclarativeI65.I72.RefPositions441.LiteralFixtureQA
open Yulang.GeneralDeclarativeI65.I72.RefPositions441.NamedGapQA
open GeneralDeclarativeWitnessSparseVariance357 (compile)
open Checker408 (Problem)
open CommonRoleOutermostResolver (Dictionary)

theorem the_original_literal_declaration_is_the_actual_and_only_visible_candidate441
    {p : Problem} (h : literalProblem = some p) :
    visible p.state.core p.root = [literal] := by
  unfold literalProblem build at h
  cases graph : compile authoredRunProjection with
  | none => simp [graph] at h
  | some sem =>
    cases book : GeneralSourceMetadataBareBundle291.compile (surface [literal]) with
    | none => simp [graph,book] at h
    | some src =>
      simp only [graph,book,Option.pure_def] at h
      cases h
      have known := congrArg GeneralSourceMetadataBareBundle291.InputBundle.declarations
        (GeneralSourceMetadataBareBundle291.preserves_input _ _ book).1
      change src.declarations = [literal] at known
      change src.declarations.filter (fun row => row.role == 7) = [literal]
      rw [known]
      rfl

theorem actual_comparable_literal_problem_still_has_no_fixed_named_selection441
    {p : Problem} (h : literalProblem = some p) :
    I72.Fits p.state literalModel ∧
      ∀ (R : SourcePrimitives) (out : Dictionary), ¬Classifies R p.state p.root (.selected out) := by
  have ⟨fits,asked,modes,_,origins⟩ := original_literal_fits_and_reads_its_route441 h
  exact ⟨fits,no_named_local_rule_can_supply_an_actual_literal_ref_selection441
    (ref := 9) (binder := 6) (int := 20)
    (the_original_literal_declaration_is_the_actual_and_only_visible_candidate441 h)
    asked rfl rfl (existing_actual_literal_kind441 h) modes (fun o read _ => ⟨.var 1,origins o read⟩)⟩

#print axioms the_original_literal_declaration_is_the_actual_and_only_visible_candidate441
#print axioms actual_comparable_literal_problem_still_has_no_fixed_named_selection441
end Yulang.GeneralDeclarativeI65.I72.RefPositions441.LiteralVisibilityQA
```

## 補足（cycle 441）— literal の次の足場と projection の正確な制限

- 元の concrete literal Problem で isolated Int leaf の実 compiler は成功、mixed outer application の legacy compiler は none。実評価は `some (true,true)`。また任意の nullary nominal tag と scalar Int は型 carrier 値として両方向とも比較不能。scalar を nominal `intKey[]` として偽装して `DeepRead` を通すのは正しい修復ではない。
- 遅延する案: 今回の scoped R21 をそのまま使い、literal 証拠の挿入は正式な後続作業へ。必要なら実 `Use env intKey 0` の primitive kind と上下の実 ordinary Int を本人の元 syntax から照合する別 leaf evidence の設計を、旧 closed assumptions を変えずに検討できる。任意の named local rule の変更だけでは足りない。これは型の受理を決め直さない。
- B3 の `f` を公開 nominal header にない finite pool slot に置くだけの符号化は、既存 source compiler の formal coverage で落ちることも証明。private universal binder を extra nominal parameter に変えてよいとは言っていない。今回の executable variance check は公開引数への projection だけ。
- declared/snapshot の実 kind 順を交換した二つの actual 正しい大きさの Problem（旧 snapshot だけが相違、もしくは両方が相違）では、body graph と current table が正しい順でも `readUse` は none、scoped check は false。誤った metadata を table で救済しない。

再現: 次の literal / stale metadata namespace は C441 EndToEnd の末尾に付加。他の二つは import を持つ単独 source。同じ production-only Lean 4.35.0 strict `--trust=0 -DwarningAsError=true`、全 exit 0。公開 47 の数には含めない。

### Literal compiler path isolation
```lean
namespace Yulang.GeneralDeclarativeI65.I72.RefPositions441.LiteralIsolationQA
open GeneralDeclarativeI65
open Yulang.GeneralDeclarativeI65.I72.RefPositions441.ScopedExample
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralSourceMetadataRows291 (interpretation)

def observedLayers : Option (Bool × Bool) :=
  literalProblem.map fun p =>
    let old := translate (authoredRegistry p.state.core.current).constructors
      (interpretation p.state.core.current.environment.source.snapshot)
    let leaf := match old (.app 20 []) with
      | some (.primitive (.scalar .int) []) => true
      | _ => false
    (leaf,(old (.app 9 [.var 6,.app 20 []])).isNone)

theorem actual_original_int_leaf_available_but_mixed_outer_blocked441 :
    observedLayers = some (true,true) := by decide +kernel

#eval observedLayers
#print axioms actual_original_int_leaf_available_but_mixed_outer_blocked441
end Yulang.GeneralDeclarativeI65.I72.RefPositions441.LiteralIsolationQA
```

### No fake scalar as a nullary nominal
```lean
import Yulang.GeneralDeclarativeI65I74RefPositionBoundary441

namespace Yulang.GeneralDeclarativeI65.I72.RefPositions441.NoFakeIntQA
open CommonNominalFullCarrier (Subtype nominal)
open CommonNominalFullDemand (Environment producerLe_iff_probe)

theorem actual_scalar_Int_is_not_a_nullary_nominal_tag441 (tag : Nat) :
    ¬ Subtype (nominal tag []) (.base .int) ∧
    ¬ Subtype (.base .int) (nominal tag []) := by
  let env : Environment Common.Row := ⟨fun _ => .bottom,fun _ => []⟩
  constructor
  · intro h
    exact (producerLe_iff_probe _ _).mp (h 0) 0 env (.base .int) rfl
  · intro h
    exact (producerLe_iff_probe _ _).mp (h 0) 0 env (.nominalHead tag 0) ⟨rfl,rfl⟩

#print axioms actual_scalar_Int_is_not_a_nullary_nominal_tag441
end Yulang.GeneralDeclarativeI65.I72.RefPositions441.NoFakeIntQA
```

### Free-pool bound on the separate rank-2 problem
```lean
import Yulang.GeneralDeclarativeI65I74RefPositionBoundary441

namespace Yulang.GeneralDeclarativeI65.I72.RefPositions441.ScopeBoundaryQA
open GeneralDeclarativeWitnessSparseVariance357 (Source Header compile valid wellFormed valid_iff)

/-- The current finite source pool covers only header formals. It does
not silently use an extra pool row as a field-local forall binder. -/
theorem unlisted_pool_name_is_not_a_private_binder441
    {nodes types rows : Nat} {s : Source nodes types rows} {p : Fin (types+rows)}
    (absent : p ∉ s.headers.flatMap (List.map Prod.snd ∘ Header.written)) :
    compile s = none := by
  cases h : valid s
  · simp [compile,h]
  · have scope := (valid_iff s).mp h
    exact (absent (scope.2.2.1 p)).elim

/-- This is a failed encoding, not a new model of the rank-2 language.
The two visible formals are written; the extra f occurs only in run. -/
def impossibleFreePoolEncoding : Source 3 1 2 :=
  ⟨[⟨9,[(.row,1),(.value,0)]⟩],
    fun i => match i.val with
    | 0 => .arrow (.inl 1) .empty (.inl 2) (.join (.var 0) (.var 1))
    | 1 => .arrow (.inr 0) .empty (.inr 0) (.var 1)
    | _ => .base .unit,
    fun _ => 0⟩

theorem actual_extra_pool_find_does_not_implement_field_rank_two441 :
    compile impossibleFreePoolEncoding = none :=
  unlisted_pool_name_is_not_a_private_binder441 (p := 2) (by decide +kernel)

#print axioms unlisted_pool_name_is_not_a_private_binder441
#print axioms actual_extra_pool_find_does_not_implement_field_rank_two441
end Yulang.GeneralDeclarativeI65.I72.RefPositions441.ScopeBoundaryQA
```

### Real stale ordered metadata
```lean
namespace Yulang.GeneralDeclarativeI65.I72.RefPositions441.StaleMetadataQA
open GeneralDeclarativeI65
open GeneralDeclarativeI65.I72.RefPositions441.ScopedExample
open GeneralDeclarativeWitnessConstructorModes357 (Environment readUse)
open GeneralDeclarativeWitnessSparseVariance357 (compile)
open GeneralSourceMetadataRows291 (Row)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open Checker408 (Problem)

def staleRows : List Row := [⟨9,some ⟨[.type,.row],9⟩,.unclassified⟩,
  ⟨20,some ⟨[],20⟩,.primitive (.scalar .int)⟩]

def altered (alsoDeclared : Bool) : InputBundle :=
  let real := surface [actual]
  ⟨(if alsoDeclared then ⟨.absent,staleRows⟩ else real.declared),
    ⟨.absent,staleRows⟩,real.roles,real.declarations⟩

def wrongSnapshot (declared : Bool) : Option Problem := do
  let actualGraph ← compile authoredRunProjection
  let book ← GeneralSourceMetadataBareBundle291.compile (altered declared)
  let env : Environment := ⟨3,1,1,authoredRunProjection,actualGraph,book⟩
  let s : GeneralDeclarativeI65.State := ⟨⟨env,ordinary,[]⟩,registry,[witnessOrigin],[]⟩
  let atlas : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,atlas⟩,⟨[71],roleDemand⟩⟩

theorem actual_graph_cannot_rescue_swapped_authored_or_snapshot_positions441
    (alsoDeclared : Bool) :
    (wrongSnapshot alsoDeclared).isSome = true ∧
    ((wrongSnapshot alsoDeclared).map fun p =>
      (readUse p.state.core.current.environment 9 2).isNone).getD false = true ∧
    test (wrongSnapshot alsoDeclared) = false := by
  cases alsoDeclared <;> decide +kernel

#print axioms actual_graph_cannot_rescue_swapped_authored_or_snapshot_positions441
end Yulang.GeneralDeclarativeI65.I72.RefPositions441.StaleMetadataQA
```
