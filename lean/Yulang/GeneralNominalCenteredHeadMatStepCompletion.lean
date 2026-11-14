import Yulang.GeneralNominalCenteredHeadMatStepAvailability

namespace Yulang.GeneralNominalCenteredHeadMatStepCompletion
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatStepKernel
open GeneralNominalCenteredHeadMatStepBoundary (boundary Local)
open GeneralNominalCenteredHeadMatStepAvailability (Extension)
variable {roles : Roles.RoleDecls} {state : State roles}

theorem selected_effect_model
    (selected : Local registry state focus (.selected key children))
    (baseline : ∃ model, Models state model ∧ GeneralNominalCenteredHeadMatStepLocal.ChosenHead registry state focus key model) :
    ∃ (effect : Effect roles) (model : GeneralNominalCommonBridge.Assignment), effect.registry = registry ∧ effect.snapshot = state.core ∧
      effect.plan.packet.site.occurrence = focus ∧ effect.plan.packet.declaration.id = key ∧
      effect.plan.packet.children = children ∧ Models state model ∧ effect.Holds model := by
  obtain ⟨model,valid,⟨otherChildren,otherUnique⟩,plan,frame,ready,head,outputs⟩ :=
    GeneralNominalCenteredHeadMatStepAvailability.chosen_effects selected baseline
  cases selected with
  | selected safe unique clear =>
      have planUnique : GeneralNominalCenteredHeadCandidates.Unique registry state.core.erased.current.context
          plan.packet.site.occurrence plan.packet.declaration.id plan.packet.children := by
        have packetKids : plan.packet.children = children := by
          have supplied := GeneralNominalCenteredHeadStepAvailability.frame_survivor
            (state := ⟨state.core,[]⟩) frame safe.1
          exact (unique.2 _ _ supplied).2
        exact frame.occurrence_eq.symm ▸ frame.key_eq.symm ▸ packetKids.symm ▸ unique
      let effect : Effect roles := ⟨registry,state.core,plan,
        frame.occurrence_eq.symm ▸ frame.key_eq.symm ▸ frame,planUnique,frame.occurrence_eq.symm ▸ ready⟩
      have packetKids : plan.packet.children = children :=
        (unique.2 _ _ (frame.occurrence_eq ▸ frame.key_eq ▸ planUnique.1)).2
      exact ⟨effect,model,rfl,rfl,frame.occurrence_eq,frame.key_eq,packetKids,valid,
        head,frame.occurrence_eq.symm ▸ outputs⟩

def SelectedCompletion (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (boundary roles).Checked registry → ∀ state root focus key children,
    B4TargetV6.Reachable (boundary roles) registry root state →
    Local registry state focus (.selected key children) →
    ∃ effect : Effect roles, effect.registry = registry ∧ effect.snapshot = state.core ∧
      effect.plan.packet.site.occurrence = focus ∧ effect.plan.packet.declaration.id = key ∧
      effect.plan.packet.children = children ∧ Extension state effect

def GeneratedSelectedChildren (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (boundary roles).Checked registry → ∀ state root focus key children,
    B4TargetV6.Reachable (boundary roles) registry root state → Stable registry state focus →
    GeneralNominalSaturationState.Generated state.core.erased.current root focus →
    Local registry state focus (.selected key children) →
    ∀ child ∈ children, GeneralNominalSaturationState.Generated state.core.erased.current root child

theorem generatedSelectedChildren (completion : SelectedCompletion roles) : GeneratedSelectedChildren roles := by
  intro registry checked state root focus key children reached stable generated selected child member
  obtain ⟨effect,registryEq,snapshot,focusEq,keyEq,childrenEq,extension⟩ :=
    completion registry checked state root focus key children reached selected
  have done := GeneralNominalCenteredHeadMatStepAvailability.stable_focus_selected_committed
    reached (focusEq.symm ▸ stable) (focusEq.symm ▸ keyEq.symm ▸ selected)
    registryEq snapshot extension
  have edge := done.2 child (childrenEq.symm ▸ member)
  exact .child generated (focusEq ▸ edge)

end Yulang.GeneralNominalCenteredHeadMatStepCompletion
