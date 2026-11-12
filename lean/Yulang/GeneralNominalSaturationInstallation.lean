import Yulang.GeneralNominalSaturationInvariants

/-! A selected source candidate with at least one where child has a real first
installation. The successor contains the entire emitted conjunction and exactly
the selected branch's model conditions. No child success is a premise. -/
namespace Yulang.GeneralNominalSaturationInstallation

open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalSaturationSteps
open GeneralNominalDemandMerging (pointSite)

variable {roles : Roles.RoleDecls}

theorem initial_selected_installation (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalLocalBoundary.Local (GeneralNominalLocalBoundary.recursiveFields roles)
      registry context root (.selected key children)) (nonempty : children ≠ []) :
    ∃ packet : Packet roles, packet.registry = registry ∧ packet.context = context ∧
      packet.site.occurrence = root ∧ packet.declaration.id = key ∧ packet.children = children ∧
      Step registry root (initial context root) (install (initial context root) packet (pointEmitted packet)) ∧
      (∀ child ∈ children, Generated (install (initial context root) packet (pointEmitted packet)) root child) ∧
      (∀ model, Models (install (initial context root) packet (pointEmitted packet)) model ↔
        GeneralNominalState.Models context.state model ∧ packet.Holds model) := by
  have survivor : GeneralNominalRecursiveCandidates.Survivor registry context root key children := by
    cases selected with | selected _ unique => exact unique.1
  obtain ⟨_,declaration,visible,checked,identity,role,bounds,located,prepared,emitted⟩ := survivor
  let packet : Packet roles := ⟨registry,context,pointSite root,declaration,checked,bounds⟩
  have exactChildren : packet.children = children := emitted.symm
  have enabled : Installable registry (initial context root) packet := by
    refine ⟨rfl,rfl,by simp [packet,initial],visible,role,located,prepared,?_,?_,?_,?_⟩
    · change GeneralNominalLocalBoundary.Local (GeneralNominalLocalBoundary.recursiveFields roles) registry context root (.selected declaration.id packet.children)
      rw [identity,exactChildren]; exact selected
    · intro prior member; cases member
    · intro other member _
      have same := List.mem_singleton.mp member; subst other; exact .refl _
    · obtain ⟨_,_,_,other,found,_,_,model,valid⟩ := prepared
      have same := Option.some.inj (located.symm.trans found); subst other
      exact ⟨model,(initial_models context root model).mpr
        (GeneralNominalRecursiveCandidates.branch_interval_sound _ _ _ _ _ _ _ valid).1,valid⟩
  have novel : ¬ Committed (initial context root) packet := by
    intro committed
    have nonempty' : packet.children ≠ [] := by rw [exactChildren]; exact nonempty
    obtain ⟨child,member⟩ := List.exists_mem_of_ne_nil _ nonempty'
    have impossible := committed.2 child member
    cases impossible
  refine ⟨packet,rfl,rfl,rfl,identity,exactChildren,⟨root,.root,.install packet (pointEmitted packet) enabled novel⟩,?_,?_⟩
  · intro child member
    exact installed_children _ packet _ child (by rw [exactChildren]; exact member)
  · intro model
    rw [install_models _ packet _ rfl model,initial_models]

end Yulang.GeneralNominalSaturationInstallation
