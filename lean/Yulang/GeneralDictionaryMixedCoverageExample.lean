import Yulang.GeneralDictionaryMixedCoverage
import Yulang.GeneralDictionaryRecordedCoverageLimit

/-! The mixed structural condition covers an actual stable recursive success
whose selected leaf is not recorded. This is a concrete test of the general
conditional dictionary theorem, not unrestricted V5. -/
namespace Yulang.GeneralDictionaryMixedCoverageExample
open GeneralDictionarySupportRecursiveExample GeneralDictionarySupportRecursiveClassification
open GeneralNominalExamples GeneralNominalSaturationState
open GeneralDeclarationExamples (roles)

theorem covered : GeneralDictionaryMixedCoverage.Covered registry finish displayRoot := by
  intro focus reached key children selected
  rcases GeneralDictionarySupportRecursiveClosure.generated_cases focus reached with rfl | rfl
  · exact Or.inl ⟨packet,by exact List.mem_singleton_self _,
      GeneralDictionaryOrdinaryTrace.packet_extension packet,rfl⟩
  · exact Or.inr (Or.inr GeneralDictionaryScalarLeaf.recursiveDisplay_covered)

/-- The generic mixed theorem is applied at the actual final context and every
one of its models, not at the earlier packet context. -/
theorem every_model (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models finish.current assignment) :
    GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context assignment
      displayRoot (.node 1 [.node 3 []]) :=
  GeneralDictionaryMixedCoverage.dictionary_evidence registry displayRoot finish
    (GeneralNominalSupportBoundary.reachable_formed registry finish displayRoot actual_reachable)
    covered assignment valid _ displayRoot .root classified

/-- The final state is reachable, stable and inhabited, with an unrecorded leaf,
yet the mixed theorem supplies the complete recursive selected dictionary. -/
theorem stable_success :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    GeneralNominalSupportSteps.Stable registry finish displayRoot ∧
    Models finish.current model ∧
    (¬ ∃ packet ∈ finish.current.packets, packet.site.occurrence = displayChild) ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context model
      displayRoot (.node 1 [.node 3 []]) :=
  ⟨actual_reachable,GeneralDictionarySupportRecursiveClosure.stable,current_model,
    GeneralDictionaryRecordedCoverageLimit.no_leaf_packet,every_model model current_model⟩
end Yulang.GeneralDictionaryMixedCoverageExample
