import Yulang.GeneralDictionaryCommittedEvidence
import Yulang.GeneralDictionaryRecursiveObstructionEvidence

/-! The cycle130 associated-output obstruction repaired by real packet
installation. Models range over the successor journal. The source inspection
context is the stored original packet context, explicitly not a claim that
regenerated local candidates have already been proved complete. -/
namespace Yulang.GeneralDictionaryCommittedEvidenceExamples

open GeneralDeclarationExamples (roles)
open GeneralDictionaryRecursiveObstruction
open GeneralNominalSaturationState GeneralNominalSaturationSteps
open GeneralNominalDemandMerging (pointSite)
open GeneralDictionaryCommittedEvidence

abbrev packet : Packet roles :=
  ⟨registry,context,pointSite root,declaration,declaration_checked,[(0,0)]⟩

theorem packet_children : packet.children = [] := by
  unfold Packet.children GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    List.mergeSort_nil]
  rfl

abbrev before : State roles := initial context root
abbrev after : State roles := install before packet (pointEmitted packet)

/-- The successor has exactly the source output refinement missing in cycle130. -/
theorem installed_models (model : GeneralNominalCommonBridge.Assignment) :
    Models after model ↔ GeneralNominalState.Models context.state model ∧
      CommonNominalFullCarrier.Equivalent (model 1).1 (.base .int) := by
  rw [install_models before packet (pointEmitted packet) rfl model,initial_models]
  change (GeneralNominalState.Models context.state model ∧
    GeneralNominalRecursiveCandidates.BranchModels registry context root declaration declaration_checked [(0,0)] model) ↔ _
  rw [branch_iff_output]
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,h⟩⟩

/-- Every successor model satisfies the terminal source Evidence, not just the
single good branch witness. -/
theorem installed_evidence (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models after model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry context model root (.node 40 []) := by
  apply (GeneralDictionaryRecursiveEvidence.evidence_leaf_iff registry context model root 40).mpr
  have source := installed_instance before packet (pointEmitted packet) (by simp) rfl
    (by decide +kernel) prepared model valid
  rw [packet_children] at source
  exact source

/-- Nonvacuity: the journal still has an actual model after installation. -/
theorem good_installed_model : Models after GeneralNominalExamples.model :=
  (install_models before packet (pointEmitted packet) rfl _).mpr
    ⟨(initial_models context root _).mpr (GeneralNominalExamples.state_models false),good_branch⟩

/-- The old countermodel is excluded by actual journal semantics. -/
theorem bad_not_installed_model : ¬ Models after badModel :=
  fun valid => bad_output_equation ((installed_models badModel).mp valid).2

/-- Installation here is an enabled source transition, not a manually asserted
semantic refinement; terminal children do not make it already committed. -/
theorem real_installation : Step registry root before after := by
  have enabled : Installable registry before packet := by
    refine ⟨rfl,rfl,by simp [before,initial],by simp,rfl,by decide +kernel,
      prepared,?_,?_,?_,?_⟩
    · rw [packet_children]
      exact selected
    · intro prior member; cases member
    · intro other member _
      have same := List.mem_singleton.mp member
      subst other
      exact .refl _
    · exact ⟨GeneralNominalExamples.model,(initial_models context root _).mpr
        (GeneralNominalExamples.state_models false),good_branch⟩
  refine ⟨root,.root,.install packet (pointEmitted packet) enabled ?_⟩
  intro committed
  have branch := committed.1 badModel ((initial_models context root _).mpr bad_original_model)
  exact bad_not_branch branch

end Yulang.GeneralDictionaryCommittedEvidenceExamples
