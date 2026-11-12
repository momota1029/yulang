import Yulang.GeneralDictionarySupportRecursiveClosure

/-! Concrete simultaneous branch witnesses for both generated nodes of the
recursive support fixture. These are actual Joint certificates, not premises
added to the concrete completion. -/
namespace Yulang.GeneralDictionarySupportRecursiveJoint
open GeneralDictionarySupportRecursiveExample GeneralDictionarySupportRecursiveClassification
open GeneralDictionarySupportRecursiveClosure
open GeneralNominalExamples
open GeneralDeclarationExamples (roles)
open GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalJointCandidates (BranchAt Joint)

private theorem branch_at (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry finish root (.selected key children))
    (m : GeneralNominalCommonBridge.Assignment)
    (instanceRule : GeneralDictionaryRecursiveEvidence.Instance registry current m root key children) :
    BranchAt registry finish.current root key m := by
  cases selected with
  | selected _ unique =>
    obtain ⟨_,a,av,ac,ak,role,ab,al,ready,ae⟩ := unique.1
    obtain ⟨b,bv,bc,bk,_,bb,bl,_,_,_,_,branch⟩ := instanceRule
    have same := GeneralDictionaryEmissionPlans.declaration_key_unique registry registry_checked a b av bv (ak.trans bk.symm)
    subst b
    exact ⟨a,av,ac,ak,role,ready,bb,bl,branch⟩

theorem parent_branch_at (m : GeneralNominalCommonBridge.Assignment) (valid : Models finish.current m) :
    BranchAt registry finish.current displayRoot 1 m :=
  branch_at displayRoot 1 [displayChild] supported_parent_selected m (parent_instance m valid)

theorem leaf_branch_at (m : GeneralNominalCommonBridge.Assignment) (valid : Models finish.current m) :
    BranchAt registry finish.current displayChild 3 m :=
  branch_at displayChild 3 [] supported_leaf_selected m
    ((GeneralDictionaryRecursiveEvidence.evidence_leaf_iff registry current m displayChild 3).mp (final_leaf_evidence m valid))

private theorem alias_equal {first last : Nat} (related : Alias finish.current first last) : first = last := by
  induction related with
  | refl => rfl
  | edge member => cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

private theorem identities_differ : displayRoot.identity ≠ displayChild.identity := by decide +kernel

theorem parent_joint : Joint registry finish.current displayRoot 1 := by
  refine ⟨?_,model,current_model,parent_branch_at model current_model,?_⟩
  · intro p member _
    have same : p = packet := List.mem_singleton.mp member
    subst p
    rfl
  · intro site related
    have member := related.1
    rw [sites_exact] at member
    rcases List.mem_cons.mp member with same | other
    · subst site
      exact parent_branch_at model current_model
    · have same := List.mem_singleton.mp other
      subst site
      exact False.elim (identities_differ (alias_equal related.2))

theorem leaf_joint : Joint registry finish.current displayChild 3 := by
  refine ⟨?_,model,current_model,leaf_branch_at model current_model,?_⟩
  · intro p member related
    have same : p = packet := List.mem_singleton.mp member
    subst p
    exact False.elim (identities_differ (alias_equal related).symm)
  · intro site related
    have member := related.1
    rw [sites_exact] at member
    rcases List.mem_cons.mp member with same | other
    · subst site
      exact False.elim (identities_differ (alias_equal related.2).symm)
    · have same := List.mem_singleton.mp other
      subst site
      exact leaf_branch_at model current_model

/-- Joint at every selected generated occurrence is a proved property of this
fixture, not an assumed journal-consistency condition. -/
theorem generated_selected_joint (focus : Occurrence roles)
    (reached : Generated finish.current displayRoot focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry finish focus (.selected key children)) :
    Joint registry finish.current focus key := by
  rcases generated_cases focus reached with rfl | rfl
  · have same := GeneralNominalLocalBoundary.local_functional selected supported_parent_selected
    have keySame := (CommonRoleOutermostResolver.Frontier.selected.inj same).1
    subst key
    exact parent_joint
  · have same := GeneralNominalLocalBoundary.local_functional selected supported_leaf_selected
    have keySame := (CommonRoleOutermostResolver.Frontier.selected.inj same).1
    subst key
    exact leaf_joint

end Yulang.GeneralDictionarySupportRecursiveJoint
