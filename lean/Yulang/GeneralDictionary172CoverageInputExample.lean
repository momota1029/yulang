import Yulang.GeneralDictionary172CoverageInput
import Yulang.GeneralDictionaryNestedRefinementExamples

/-! The existing inhabited two-level nominal source exercises discovery at
physical slot zero. Its other nonpoint interval is not conflated with this
point-root theorem. No preconstructed Spine is supplied. -/
namespace Yulang.GeneralDictionary172CoverageInputExample
open GeneralDictionary172CoverageInput
open GeneralNominalRecursiveInspection
open GeneralNominalProvenanceSource
open GeneralDictionaryNestedRefinementExamples (query)

theorem finite_syntax : Syntax (fun _ : Fin 1 => 7) query := by
  apply Syntax.wrap
  exact Syntax.leaf 0

theorem actual_finished : Finished (inspect state query (0,0) none) := by
  unfold Finished
  decide +kernel

theorem actual_points : GeneralDictionary171LocalInspectionObservation.PointInspection state
    (inspect state query (0,0) none) :=
  GeneralDictionary171RequestChecker.pointReport_sound _ _ (by decide +kernel)

theorem nested_extracted :
    ∃ bounds : Fin 1 → GeneralNominalInspection.Bounds state,
      ∃ spine : GeneralNominalSpineFacts.Spine state (fun _ => 7) bounds 0,
        spine.query = query :=
  inspected_spine state (fun _ => 7) finite_syntax 0 none actual_finished actual_points

theorem inhabited_nested :
    GeneralNominalState.Models state (model .bottom .top .bottom) ∧
    ∃ bounds : Fin 1 → GeneralNominalInspection.Bounds state,
      ∃ spine : GeneralNominalSpineFacts.Spine state (fun _ => 7) bounds 0,
        spine.query = query :=
  ⟨source_models _ _ _,nested_extracted⟩
end Yulang.GeneralDictionary172CoverageInputExample
