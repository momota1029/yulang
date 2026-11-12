import Yulang.GeneralDictionaryOutputMergeAllModels
import Yulang.GeneralDictionaryRecursiveEvidenceReadback

/-! Exact payload for this concrete reachable output-merge fixture only.
There are two ordered terminal occurrences, not a deduplicated child set.
No general principal-dictionary or resolver completeness theorem is claimed. -/
namespace Yulang.GeneralDictionaryOutputMergeExactPayload
open GeneralDictionaryOutputMergeSuccess
open GeneralDictionaryOutputMergeRootEvidence (rootPayload)
open GeneralDictionaryRecursiveEvidence
open GeneralDictionaryReadback (Payload PayloadEvidence)
open GeneralNominalExamples (displayRoot model)
open GeneralNominalCommonBridge (Assignment)

theorem child_instance_shape (m : Assignment) (n key : Nat)
    (cs : List (GeneralSourceDictionaries.Occurrence GeneralDeclarationExamples.roles))
    (rule : Instance registry current m (child n) key cs) : key = 7 ∧ cs = [] := by
  have saved := rule
  obtain ⟨d,visible,checked,identity,role,rest⟩ := rule
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · cases role
  · have equal : key = 7 := identity.symm
    subst key
    exact ⟨rfl,instance_children_functional registry registry_checked current m model (child n) 7 cs []
      saved (current_terminal_instance n)⟩

theorem parent_instance_shape (m : Assignment) (key : Nat)
    (cs : List (GeneralSourceDictionaries.Occurrence GeneralDeclarationExamples.roles))
    (rule : Instance registry current m displayRoot key cs) :
    key = 1 ∧ cs = [child 10,child 11] := by
  have saved := rule
  obtain ⟨d,visible,checked,identity,role,rest⟩ := rule
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · have equal : key = 1 := identity.symm
    subst key
    exact ⟨rfl,instance_children_functional registry registry_checked current m model displayRoot 1 cs _
      saved GeneralDictionaryOutputMergeRootEvidence.current_parent_instance⟩
  · cases role

theorem child_payload_exact (m : Assignment) (n : Nat) (payload : Payload)
    (tree : PayloadEvidence (Instance registry current m) (child n) payload) :
    payload = .node 7 [] := by
  cases tree with
  | node rule kids =>
    obtain ⟨rfl,rfl⟩ := child_instance_shape m n _ _ rule
    cases kids
    rfl

theorem root_payload_exact (m : Assignment) (payload : Payload)
    (evidence : Evidence registry current m displayRoot payload) : payload = rootPayload := by
  have tree := (evidence_iff_payload registry current m displayRoot payload).mp evidence
  cases tree with
  | node rule kids =>
    obtain ⟨rfl,rfl⟩ := parent_instance_shape m _ _ rule
    cases kids with
    | cons one rest =>
      cases rest with
      | cons two rest =>
        cases rest
        rw [child_payload_exact m 10 _ one,child_payload_exact m 11 _ two]

/-- Every final model validates exactly the ordered root payload in this
fixture. The forward uniqueness implication above requires no model premise. -/
theorem evidence_iff_exact (m : Assignment) (valid : GeneralNominalSaturationState.Models finish.current m)
    (payload : Payload) : Evidence registry current m displayRoot payload ↔ payload = rootPayload := by
  constructor
  · exact root_payload_exact m payload
  · intro equal
    subst payload
    exact GeneralDictionaryOutputMergeAllModels.full_dictionary m valid
end Yulang.GeneralDictionaryOutputMergeExactPayload
