import Yulang.GeneralDictionaryScalarMerge
import Yulang.GeneralDictionaryJointMergeExample

/-! The nonempty regression discharges output equality from actual generated
requests, rather than from an independently supplied AssociatedMeaning. -/
namespace Yulang.GeneralDictionaryScalarMergeExample
open GeneralDictionaryJointMergeExample

theorem generated_output_equations :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalDemandMerging.outputAtoms first last) := by
  apply GeneralDictionaryScalarMerge.output_atoms_of_scalar_tests registry before first last
    terminal terminal terminal_checked terminal_checked [(1,1)] [(1,1)] model
    (branch_models 200 1 (by decide)) (branch_models 201 3 (by decide)) (fun _ => .int)
  all_goals
    intro output member
    have eq := List.mem_singleton.mp member
    subst output
    simp only [before,first,last,GeneralNominalDemandMerging.pointSite]
    rw [schema_exact]
    exact List.mem_singleton_self _

theorem complete_evidence_from_requests :
    GeneralDictionaryRecursiveEvidence.Evidence registry
      (GeneralNominalSaturationState.merge before first last).context model first.occurrence (.node 7 []) ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry
      (GeneralNominalSaturationState.merge before first last).context model last.occurrence (.node 7 []) := by
  constructor
  · exact (GeneralDictionaryJointMerge.evidence_merge_iff ..).mpr
      ⟨source_evidence 200 1 (Or.inl rfl),generated_output_equations⟩
  · exact (GeneralDictionaryJointMerge.evidence_merge_iff ..).mpr
      ⟨source_evidence 201 3 (Or.inr rfl),generated_output_equations⟩
end Yulang.GeneralDictionaryScalarMergeExample
