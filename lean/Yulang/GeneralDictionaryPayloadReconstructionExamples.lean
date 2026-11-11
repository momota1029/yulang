import Yulang.GeneralDictionaryPayloadReconstruction
import Yulang.GeneralDictionaryHeadlessFixture

/-!
# Raw selected-key dictionary reconstruction regressions

Canonical declaration emissions recover descendant occurrences, including the
fixture's nonidentity source map. Missing and extra children defer rather than
being truncated. These checks assert structural plans, not candidate feasibility.
-/
namespace Yulang.GeneralDictionaryPayloadReconstructionExamples
open GeneralDictionaryHeadlessFixture
open GeneralDictionaryPayloadReconstruction
open GeneralSourceDictionaries

abbrev payload : GeneralDictionaryReadback.Payload := .node 2 [.node 3 []]
abbrev sourceTree : Dictionary roles := .node root 2 [.node child 3 []]

private theorem root_plan_lookup :
    GeneralDictionaryPlanLookup.lookup registry registry_checked frame root 2 = some [child] := by
  apply (GeneralDictionaryPlanLookup.lookup_exact registry registry_checked frame root 2 [child]).mpr
  exact ⟨binderWrap, by simp, rfl, rfl, root_actual_children.symm⟩

private theorem child_plan_lookup :
    GeneralDictionaryPlanLookup.lookup registry registry_checked frame child 3 = some [] := by
  apply (GeneralDictionaryPlanLookup.lookup_exact registry registry_checked frame child 3 []).mpr
  exact ⟨leaf, by simp, rfl, rfl, child_actual_children.symm⟩

theorem leaf_reconstructed :
    reconstruct registry registry_checked (fun _ => frame) (.node 3 []) child =
      some (.node child 3 []) := by
  apply reconstruct_complete registry registry_checked (fun _ => frame) (.node child 3 [])
  exact .node ((GeneralDictionaryPlanLookup.lookup_exact registry registry_checked frame child 3 []).mp child_plan_lookup)
    (by simp)

/-- No recursive source occurrence recipe is an input. -/
theorem tree_reconstructed :
    reconstruct registry registry_checked (fun _ => frame) payload root = some sourceTree := by
  apply reconstruct_complete registry registry_checked (fun _ => frame) sourceTree
  apply Evidence.node
  · exact (GeneralDictionaryPlanLookup.lookup_exact registry registry_checked frame root 2 [child]).mp root_plan_lookup
  · intro tree member
    have same := List.mem_singleton.mp member
    subst tree
    exact (reconstruct_sound registry registry_checked (fun _ => frame) (.node 3 []) child _ leaf_reconstructed).2

theorem omitted_child_defers :
    reconstruct registry registry_checked (fun _ => frame) (.node 2 []) root = none := by
  rw [reconstruct, root_plan_lookup]
  change (reconstructChildren registry registry_checked (fun _ => frame) [] [child]).bind
    (fun trees => some (Dictionary.node root 2 trees)) = none
  rw [reconstructChildren]
  rfl

/-- A duplicated extra raw child must not be silently dropped. -/
theorem extra_child_defers :
    reconstruct registry registry_checked (fun _ => frame)
      (.node 2 [.node 3 [], .node 3 []]) root = none := by
  rw [reconstruct, root_plan_lookup]
  change (reconstructChildren registry registry_checked (fun _ => frame) [.node 3 [], .node 3 []] [child]).bind
    (fun trees => some (Dictionary.node root 2 trees)) = none
  rw [reconstructChildren, leaf_reconstructed]
  change ((reconstructChildren registry registry_checked (fun _ => frame) [.node 3 []] []).bind
    (fun trees => some (Dictionary.node child 3 [] :: trees))).bind
    (fun trees => some (Dictionary.node root 2 trees)) = none
  rw [reconstructChildren]
  rfl

theorem wrong_role_key_defers :
    reconstruct registry registry_checked (fun _ => frame) (.node 3 []) root = none := by
  have absent : GeneralDictionaryPlanLookup.lookup registry registry_checked frame root 3 = none := by
    apply (GeneralDictionaryPlanLookup.lookup_none registry registry_checked frame root 3).mpr
    rintro demands ⟨declaration, present, identity, role, _⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · cases identity
    · cases role
  rw [reconstruct, absent]
  rfl

theorem absent_key_defers :
    reconstruct registry registry_checked (fun _ => frame) (.node 99 []) root = none := by
  have absent : GeneralDictionaryPlanLookup.lookup registry registry_checked frame root 99 = none := by
    apply (GeneralDictionaryPlanLookup.lookup_none registry registry_checked frame root 99).mpr
    rintro demands ⟨declaration, present, identity, _, _⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> cases identity
  rw [reconstruct, absent]
  rfl

/-- The computed child keeps source identity 20 rather than its list index. -/
theorem source_identities_preserved :
    ∃ reconstructed, reconstruct registry registry_checked (fun _ => frame) payload root =
      some reconstructed ∧ (observations reconstructed).map (fun event => event.1.identity) = [9, 20] :=
  ⟨sourceTree, tree_reconstructed, rfl⟩

/-- The exact original runtime payload is retained alongside Plan evidence. -/
theorem source_readback : Readback root payload sourceTree ∧
    Evidence (Rule registry registry_checked (fun _ => frame)) sourceTree :=
  reconstruct_sound registry registry_checked (fun _ => frame) payload root sourceTree tree_reconstructed

end Yulang.GeneralDictionaryPayloadReconstructionExamples
