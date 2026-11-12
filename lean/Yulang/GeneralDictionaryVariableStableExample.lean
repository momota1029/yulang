import Yulang.GeneralDictionaryVariableStableCoverage
import Yulang.GeneralDictionaryUnrecordedAliasLeafExample

/-! A nonempty-journal regression of the stable structural-coverage theorem.
The parent is historical, the leaf is unrecorded; no terminal-only dictionary
or empty-journal shortcut is used. This does not exercise a nontrivial alias class. -/
namespace Yulang.GeneralDictionaryVariableStableExample
open GeneralDictionarySupportRecursiveExample GeneralDictionarySupportRecursiveClassification
open GeneralNominalExamples GeneralNominalSaturationState
open GeneralDeclarationExamples (roles)

theorem covered : GeneralDictionaryVariableStableCoverage.Covered registry finish displayRoot := by
  intro focus reached key children selected
  rcases GeneralDictionarySupportRecursiveClosure.generated_cases focus reached with rfl | rfl
  · exact Or.inl ⟨packet,List.mem_singleton_self _,rfl⟩
  · refine Or.inr ⟨intDisplay,by simp,int_display_checked,
      Or.inr (Or.inr ⟨GeneralDictionaryUnrecordedAliasLeafExample.shape⟩),?_⟩
    intro site related
    obtain ⟨shape,k,cs,chosen⟩ := GeneralDictionaryUnrecordedAliasLeafExample.covered site related
    exact ⟨Or.inr shape,k,cs,chosen⟩

theorem every_model (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models finish.current assignment) :
    GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context assignment
      displayRoot (.node 1 [.node 3 []]) :=
  GeneralDictionaryVariableStableCoverage.dictionary_evidence registry displayRoot (context true)
    initial_source finish GeneralDictionaryRecordedCoverageLimit.ordinary_trace
    GeneralDictionarySupportRecursiveClosure.stable covered assignment valid _ displayRoot .root classified

theorem reachable_stable_unrecorded_success :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    GeneralNominalSupportSteps.Stable registry finish displayRoot ∧
    Models finish.current model ∧
    (¬ ∃ packet ∈ finish.current.packets, packet.site.occurrence = displayChild) ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context model
      displayRoot (.node 1 [.node 3 []]) :=
  ⟨actual_reachable,GeneralDictionarySupportRecursiveClosure.stable,current_model,
    GeneralDictionaryRecordedCoverageLimit.no_leaf_packet,every_model model current_model⟩
end Yulang.GeneralDictionaryVariableStableExample
