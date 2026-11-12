import Yulang.GeneralDictionaryOutputMergeAllModels

/-! Current branch compatibility and Joint for the same reachable output-merge
fixture. All-model Instance supplies semantic facts; the separately proved
Linked/Fresh obligations supply current Prepared. No source-instance judgment
is silently identified with candidate availability. -/
namespace Yulang.GeneralDictionaryOutputMergeJointModels
open GeneralDictionaryOutputMergeSuccess
open GeneralNominalExamples (displayRoot model)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalSaturationState GeneralNominalJointCandidates
open GeneralDictionaryRecursiveEvidence (Instance Evidence)
open GeneralDictionaryOutputMergeAllModels

/-- The missing operational preparation side conditions are explicit. -/
theorem branch_of_instance (root : Occurrence GeneralDeclarationExamples.roles)
    (key : Nat) (children : List (Occurrence GeneralDeclarationExamples.roles)) (m : Assignment)
    (linked : GeneralNominalState.Linked current.state root.demand)
    (fresh : GeneralNominalAllocation.Fresh current.state registry root.identity)
    (instanceRule : Instance registry current m root key children) :
    BranchAt registry finish.current root key m := by
  obtain ⟨d,visible,checked,identity,role,bounds,located,finished,ready,emitted,metadata,branch⟩ := instanceRule
  exact ⟨d,visible,checked,identity,role,
    ⟨metadata,linked,fresh,bounds,located,finished,ready,m,branch⟩,bounds,located,branch⟩

theorem root_linked : GeneralNominalState.Linked current.state displayRoot.demand := by
  constructor
  · intro index
    have member : 0 ∈ GeneralNominalState.sources current.state :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨(0 : Fin 2),rfl⟩)))
    exact ⟨member,member⟩
  · intro output member; cases member

theorem root_branch (m : Assignment) (valid : Models finish.current m) :
    BranchAt registry finish.current displayRoot 1 m :=
  branch_of_instance displayRoot 1 [child 10,child 11] m root_linked (current_fresh _)
    (GeneralDictionaryOutputMergeAllModels.current_parent_instance m valid)

theorem child_branch (m : Assignment) (valid : Models finish.current m)
    (n : Nat) (which : n = 10 ∨ n = 11) :
    BranchAt registry finish.current (child n) 7 m :=
  branch_of_instance (child n) 7 [] m (child_linked n which) (current_fresh _)
    (GeneralDictionaryOutputMergeAllModels.current_terminal_instance m valid n which)

theorem root_alias_identity (identity : Nat)
    (related : Alias finish.current displayRoot.identity identity) : displayRoot.identity = identity := by
  rcases GeneralDictionarySupportChoices.alias_merge_cases before.current (site 10) (site 11)
    displayRoot.identity identity related with old | ⟨left,_⟩ | ⟨left,_⟩
  · exact old_alias_eq old
  · exact False.elim (first_not_parent (old_alias_eq left).symm)
  · exact False.elim (last_not_parent (old_alias_eq left).symm)

theorem root_joint (m : Assignment) (valid : Models finish.current m) :
    Joint registry finish.current displayRoot 1 := by
  refine ⟨?_,m,valid,root_branch m valid,?_⟩
  · intro committed member _
    have eq := List.mem_singleton.mp member; subst committed
    rfl
  · intro childSite related
    have member := related.1
    rw [sites_exact] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact root_branch m valid
    · exact False.elim (first_not_parent (root_alias_identity _ related.2).symm)
    · exact False.elim (last_not_parent (root_alias_identity _ related.2).symm)

theorem child_joint (m : Assignment) (valid : Models finish.current m) :
    Joint registry finish.current (child 10) 7 := by
  refine ⟨?_,m,valid,child_branch m valid 10 (Or.inl rfl),?_⟩
  · intro committed member related
    have eq := List.mem_singleton.mp member; subst committed
    rcases merged_alias_identity _ related with left | right
    · exact False.elim (first_not_parent left)
    · exact False.elim (last_not_parent right)
  · intro childSite related
    have member := related.1
    rw [sites_exact] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · rcases merged_alias_identity _ related.2 with left | right
      · exact False.elim (first_not_parent left)
      · exact False.elim (last_not_parent right)
    · exact child_branch m valid 10 (Or.inl rfl)
    · exact child_branch m valid 11 (Or.inr rfl)

/-- Inhabitance is exhibited separately from the universal implication. -/
theorem inhabited_joint_and_universal_evidence :
    Models finish.current model ∧
    Joint registry finish.current displayRoot 1 ∧
    Joint registry finish.current (child 10) 7 ∧
    ∀ m, Models finish.current m →
      Evidence registry current m displayRoot GeneralDictionaryOutputMergeRootEvidence.rootPayload :=
  ⟨finish_model,root_joint model finish_model,child_joint model finish_model,full_dictionary⟩

end Yulang.GeneralDictionaryOutputMergeJointModels
