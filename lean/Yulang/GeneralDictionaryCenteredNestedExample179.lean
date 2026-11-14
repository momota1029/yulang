import Yulang.GeneralDictionaryCenteredNested179

/-! Regression for the accepted nested syntax and inhabited actual source.
The source regression exercises discovery, not G reachability or stable selection. -/
namespace Yulang.GeneralDictionaryCenteredNestedExample179
open GeneralNominalInspection (Query)
open GeneralDictionary172CoverageSyntax
open GeneralDictionary172CoverageInput
open GeneralNominalRecursiveInspection
open GeneralNominalProvenanceSource (state)
open GeneralDictionaryNestedRefinementExamples (query)

 theorem nested_recognized : recognize (fun _ : Fin 1 => 7) query = true := by decide +kernel

 theorem not_unary : recognize (fun _ : Fin 1 => 7)
    (.nominal 0 [.nominal 0 [.variables [7]], .nominal 0 [.variables [7]]]) = false := by decide +kernel

 theorem actual_discovery :
    ∃ bounds : Fin 1 → GeneralNominalInspection.Bounds state,
      ∃ spine : GeneralNominalSpineFacts.Spine state (fun _ => 7) bounds 0,
        spine.query = query :=
  recognized_spine state (fun _ => 7) nested_recognized 0 none
    GeneralDictionary172CoverageInputExample.actual_finished
    GeneralDictionary172CoverageInputExample.actual_points

 theorem inhabited_discovery :
    GeneralNominalState.Models state (GeneralNominalProvenanceSource.model .bottom .top .bottom) ∧
    Finished (inspect state query (0,0) none) ∧
    GeneralDictionary171LocalInspectionObservation.PointInspection state (inspect state query (0,0) none) ∧
    ∃ bounds : Fin 1 → GeneralNominalInspection.Bounds state,
      ∃ spine : GeneralNominalSpineFacts.Spine state (fun _ => 7) bounds 0,
        spine.query = query :=
  ⟨GeneralNominalProvenanceSource.source_models _ _ _,
    GeneralDictionary172CoverageInputExample.actual_finished,
    GeneralDictionary172CoverageInputExample.actual_points,actual_discovery⟩
end Yulang.GeneralDictionaryCenteredNestedExample179
