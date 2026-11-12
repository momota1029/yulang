import Yulang.GeneralNominalSupportBoundary

/-! A guarded selected initial occurrence with where-children has a real first
installation. Support and consistency are extracted from the independent
classifier; no successful child dictionary is assumed. -/
namespace Yulang.GeneralNominalSupportInstallation

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps

variable {roles : Roles.RoleDecls}

theorem initial_selected_installation (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry (GeneralNominalSupport.initial context root) root
      (.selected key children)) (nonempty : children ≠ []) :
    ∃ packet : Packet roles, ∃ support,
      packet.site.occurrence = root ∧ packet.declaration.id = key ∧ packet.children = children ∧
      Step registry root (GeneralNominalSupport.initial context root)
        (GeneralNominalSupportSteps.install (GeneralNominalSupport.initial context root) packet support) := by
  classical
  have survivor : GeneralNominalRecursiveCandidates.Survivor registry context root key children := by
    cases selected with | selected _ unique => exact unique.1
  obtain ⟨_,declaration,visible,checked,identity,role,bounds,located,prepared,emitted⟩ := survivor
  let packet : Packet roles := ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,checked,bounds⟩
  have exactChildren : packet.children = children := emitted.symm
  have decision : ∃ support, DecisionGuard (GeneralNominalSupport.initial context root) registry root support := by
    by_cases known : ∃ support, DecisionGuard (GeneralNominalSupport.initial context root) registry root support
    · exact known
    · cases selected with | selected safe _ => exact False.elim (safe.2.2.2 (Or.inr known))
  obtain ⟨support,decision⟩ := decision
  have guard : PacketGuard (GeneralNominalSupport.initial context root) packet support :=
    ⟨⟨decision.1,decision.2.1,decision.2.2 declaration visible role bounds located⟩,decision⟩
  have old : GeneralNominalFeedbackK2.Local registry (GeneralNominalSaturationState.initial context root) root
      (.selected declaration.id packet.children) := by
    rw [identity,exactChildren]
    exact GeneralNominalSupportBoundary.selected_old selected
  have enabled : GeneralNominalFeedbackSteps.Installable registry
      (GeneralNominalSaturationState.initial context root) packet := by
    have preparation := prepared
    obtain ⟨_,_,_,other,found,_,_,model,branch⟩ := preparation
    have equal := Option.some.inj (located.symm.trans found)
    subst other
    refine ⟨⟨rfl,rfl,by simp [packet,GeneralNominalSaturationState.initial],visible,role,located,prepared,
      GeneralNominalFeedbackK2.selected_legacy old,?_,?_,?_,?_⟩,old,?_⟩
    · intro prior member; cases member
    · intro other member _
      have same := List.mem_singleton.mp member; subst other; exact .refl _
    · exact ⟨model,(initial_models ..).mpr
        (GeneralNominalRecursiveCandidates.branch_interval_sound _ _ _ _ _ _ _ branch).1,branch⟩
    · exact GeneralNominalJointCandidates.initial_joint registry context root declaration visible checked role bounds located prepared model branch
    · intro other member _
      have same := List.mem_singleton.mp member; subst other; exact .refl _
  refine ⟨packet,support,rfl,identity,exactChildren,root,.root,.install packet support enabled ?_ guard⟩
  intro committed
  cases listed : children with
  | nil => exact nonempty listed
  | cons child rest =>
    have absent := committed.2 child (by rw [exactChildren,listed]; simp)
    cases absent

end Yulang.GeneralNominalSupportInstallation
