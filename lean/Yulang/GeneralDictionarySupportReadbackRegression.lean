import Yulang.GeneralDictionarySupportRecursiveJoint
import Yulang.GeneralDictionarySupportReadback
import Yulang.B4TargetV3Functionality

/-! Nonempty, inhabited, stable recursive regression for finite support readback.
The accessibility proof uses only the two local selected shapes, not Classify. -/
namespace Yulang.GeneralDictionarySupportReadbackRegression
open GeneralDictionarySupportRecursiveExample GeneralDictionarySupportRecursiveClassification
open GeneralDictionarySupportRecursiveClosure GeneralDictionarySupportRecursiveJoint
open GeneralNominalExamples
open GeneralDeclarationExamples (roles)
open CommonRoleOutermostResolver GeneralNominalSaturationState

abbrev actualLocal := B4TargetV3.Local
  (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry finish

/-- The independent current child relation is a one-edge acyclic relation
below this root. No completed dictionary is used in this proof. -/
theorem accessible : Acc (Child actualLocal) displayRoot := by
  have leafLocal := (GeneralNominalSupportBoundary.local_correspondence registry finish displayChild _).mpr
    supported_leaf_selected
  have rootLocal := (GeneralNominalSupportBoundary.local_correspondence registry finish displayRoot _).mpr
    supported_parent_selected
  have leafAcc : Acc (Child actualLocal) displayChild := by
    refine .intro _ ?_
    intro child edge
    obtain ⟨key,children,localRule,member⟩ := edge
    have same := (Frontier.selected.inj (B4TargetV3.local_functional localRule leafLocal)).2
    rw [same] at member
    cases member
  refine .intro _ ?_
  intro child edge
  obtain ⟨key,children,localRule,member⟩ := edge
  have same := (Frontier.selected.inj (B4TargetV3.local_functional localRule rootLocal)).2
  rw [same] at member
  have equal := List.mem_singleton.mp member
  subst child
  exact leafAcc

theorem generated_selected (focus : GeneralSourceDictionaries.Occurrence roles)
    (reached : Generated finish.current displayRoot focus) :
    ∃ key children, GeneralNominalSupportBoundary.Local registry finish focus (.selected key children) := by
  rcases generated_cases focus reached with rfl | rfl
  · exact ⟨1,[displayChild],supported_parent_selected⟩
  · exact ⟨3,[],supported_leaf_selected⟩

/-- Apply the generic readback theorem with every premise discharged by the
concrete source trace; Classify and Evidence are outputs, not regression inputs. -/
theorem extracted : ∃ dictionary,
    B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry finish displayRoot (.selected dictionary) ∧
    ∀ model, Models finish.current model →
      GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context model displayRoot dictionary :=
  GeneralDictionarySupportReadback.uniform_dictionary registry finish displayRoot
    actual_reachable stable generated_selected generated_selected_joint accessible

/-- The independently extracted payload is exactly the ordered two-node
source dictionary, by functionality of the independent classification. -/
theorem extracted_exact : ∃ dictionary : Dictionary,
    dictionary = .node 1 [.node 3 []] ∧
    B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry finish displayRoot (.selected dictionary) ∧
    ∀ model, Models finish.current model →
      GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context model displayRoot dictionary := by
  obtain ⟨dictionary,derived,sound⟩ := extracted
  have same := Result.selected.inj (B4TargetV3.classify_functional derived classified)
  exact ⟨dictionary,same,derived,sound⟩
end Yulang.GeneralDictionarySupportReadbackRegression
