import Yulang.GeneralDictionaryCenteredNested179
import Yulang.GeneralDictionaryCenteredNominalPointExample178

/-! Outer pointness does not imply the retained structural PointInspection
restriction. An inhabited centered candidate has a completed nominal inspection
whose descriptor carries two distinct inner endpoints. This is not a
counterexample to G: no ground reachability or stable selection is asserted. -/
namespace Yulang.GeneralDictionaryCenteredNestedLimit179
open GeneralNominalRecursiveInspection
open GeneralDictionary171LocalInspectionObservation (PointInspection)
open GeneralDictionaryNominalPairExample178 (state context declaration descriptor assignment registry)
open GeneralDictionaryCenteredNominalPointExample178 (root start plan candidate inhabited evidence)

 theorem outer_point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2 := by
  intro index; rfl

 theorem completed : Finished (inspect state (.nominal 0 [.variables [0]]) (0,0) none) := by
  unfold Finished
  decide +kernel

 theorem inner_nonpoint : descriptor.arguments = [.type (2,3)] ∧ (2 : Fin state.base.slots) ≠ 3 :=
  ⟨rfl,by decide +kernel⟩

 theorem not_point_inspection : ¬ PointInspection state
    (inspect state (.nominal 0 [.variables [0]]) (0,0) none) := by
  intro points
  have member : (0,0) ∈ (inspect state (.nominal 0 [.variables [0]]) (0,0) none).inspected := by decide +kernel
  obtain ⟨n,slots,parameters⟩ := points (0,0) member descriptor rfl
  have len := congrArg List.length parameters
  have one : n = 1 := by simpa using len.symm
  subst n
  have pair : (2 : Fin 4) = slots 0 ∧ (3 : Fin 4) = slots 0 := by
    simpa [descriptor,List.ofFn_succ] using parameters
  have impossible : (2 : Fin 4) = 3 := pair.1.trans pair.2.symm
  exact (by decide +kernel : (2 : Fin 4) ≠ 3) impossible

 theorem inhabited_point_candidate_without_structural_points :
    GeneralNominalCenteredSteps.Models start (assignment false) ∧
    GeneralDictionaryCenteredCandidate176.Candidate registry start root declaration.id [] plan ∧
    (∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) ∧
    Finished (inspect state (.nominal 0 [.variables [0]]) (0,0) none) ∧
    ¬ PointInspection state (inspect state (.nominal 0 [.variables [0]]) (0,0) none) :=
  ⟨inhabited false,candidate,outer_point,completed,not_point_inspection⟩

/-- The older leaf fragment succeeds here; failure of this structural check
is not failure of semantic evidence or of the language. -/
 theorem evidence_despite_failed_structural_check :
    GeneralDictionaryRecursiveEvidence.Evidence registry context (assignment false) root (.node declaration.id []) ∧
    ¬ PointInspection state (inspect state (.nominal 0 [.variables [0]]) (0,0) none) :=
  ⟨evidence false,not_point_inspection⟩
end Yulang.GeneralDictionaryCenteredNestedLimit179
