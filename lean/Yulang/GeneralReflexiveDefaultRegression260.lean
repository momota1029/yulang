import Yulang.GeneralReflexiveDefaultRun260
namespace Yulang.GeneralReflexiveDefaultRegression260
open GeneralDictionaryAllocDefaultSource202
open GeneralDictionaryVersionedDefault202233 (current)
open GeneralReflexiveDefaultSource260 (facts initialState finalState observe)
open GeneralReflexiveDefaultModels260 (Models)
open GeneralNominalCommonBridge (Assignment)

theorem old_no_step (after) : ¬ GeneralNominalVersionedKernel232.Step registry root current after := by
 rintro ⟨focus,generated,action⟩
 exact GeneralDictionaryVersionedDefault202Local233.stable focus generated after action

/-- Recording an already implied finite fact is a semantic stutter, not a
new old-kernel installation or a strict refinement of its model set. -/
theorem fact_step_semantic_stutter :
 GeneralRebaseStep258.Step observe initialState finalState ∧
 (∀ assignment, Models initialState assignment ↔ Models finalState assignment) ∧
 (∀ after, ¬ GeneralNominalVersionedKernel232.Step registry root current after) :=
 ⟨GeneralReflexiveDefaultRun260.first_step,
   GeneralReflexiveDefaultModels260.same_assignment initialState finalState,old_no_step⟩

theorem no_strict_model_refinement : ¬ ∃ assignment, Models initialState assignment ∧ ¬ Models finalState assignment := by
 rintro ⟨assignment,initial,missing⟩
 exact missing ((GeneralReflexiveDefaultModels260.same_assignment initialState finalState assignment).mp initial)

theorem run_certificate (assignment : Assignment)
 (source : GeneralNominalVersionedJournal232.Models current assignment) :
 GeneralReflexiveDefaultRun260.run initialState = .ok (some finalState) ∧ Models finalState assignment ∧
 GeneralNominalVersionedEvidence231.Evidence registry current.core assignment root (.node 37 []) := by
 have final := (GeneralReflexiveDefaultModels260.models_exact finalState assignment).mpr source
 exact ⟨GeneralReflexiveDefaultRun260.first,final,GeneralReflexiveDefaultModels260.evidence finalState assignment final⟩
end Yulang.GeneralReflexiveDefaultRegression260
