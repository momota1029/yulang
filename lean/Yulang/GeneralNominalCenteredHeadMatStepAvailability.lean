import Yulang.GeneralNominalCenteredHeadMatStepTrace

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadMatStepAvailability
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatStepKernel
open GeneralNominalCenteredHeadMatStepBoundary (Local boundary)
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}

theorem selected_frame
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (selected : Local registry state focus (.selected key children)) :
    ∃ plan, GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan ∧ plan.packet.children = children := by
  obtain ⟨center,recorded,centerEq⟩ := (GeneralNominalCenteredHeadMatStepBoundary.selected_ready selected).1
  obtain ⟨first,⟨context,labels,source,point,ground,coverage,rfl⟩,path⟩ := reachable
  obtain ⟨raw,rawRecorded,rawEq⟩ := GeneralNominalCenteredHeadMatStepTrace.centered_registered path center recorded
  have rawFocus := rawEq.trans centerEq
  cases selected with
  | selected safe unique clear =>
      obtain ⟨known,declaration,visible,checked,keyEq,role,bounds,located,prepared,childrenEq⟩ := unique.1
      let packet : GeneralNominalSaturationState.Packet roles :=
        ⟨registry,state.core.erased.current.context,raw,declaration,checked,bounds⟩
      let plan : Plan roles := ⟨packet,center,rawEq.symm⟩
      refine ⟨plan,⟨rfl,rfl,rawFocus,keyEq,rawRecorded,recorded,visible,role,located,prepared⟩,?_⟩
      change GeneralNominalAllocation.children _ registry raw.occurrence declaration checked _ = _
      rw [rawFocus,childrenEq]
      rfl

theorem selected_effect (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (selected : Local registry state focus (.selected key children)) :
    ∃ effect : Effect roles, effect.registry = registry ∧ effect.snapshot = state.core ∧
      effect.plan.packet.site.occurrence = focus ∧ effect.plan.packet.declaration.id = key ∧
      effect.plan.packet.children = children := by
  obtain ⟨plan,frame,kids⟩ := selected_frame reachable selected
  have ready := GeneralNominalCenteredHeadMatStepTrace.ready checked reachable frame
  cases selected with
  | selected safe unique clear =>
      have unique' : GeneralNominalCenteredHeadCandidates.Unique registry state.core.erased.current.context
          plan.packet.site.occurrence plan.packet.declaration.id plan.packet.children :=
        frame.occurrence_eq.symm ▸ frame.key_eq.symm ▸ kids.symm ▸ unique
      let effect : Effect roles := ⟨registry,state.core,plan,
        frame.occurrence_eq.symm ▸ frame.key_eq.symm ▸ frame,unique',frame.occurrence_eq.symm ▸ ready⟩
      exact ⟨effect,rfl,rfl,frame.occurrence_eq,frame.key_eq,kids⟩

theorem selected_safe (selected : Local registry state root (.selected key children))
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core root selectedKey plan) :
    GeneralNominalCenteredHeadMatStepCycles.Safe state plan := by
  refine ⟨GeneralNominalCenteredInspection.plan_complete plan ?_,?_⟩
  · have located := frame.located
    rw [← frame.occurrence_eq,← plan.input_exact] at located
    exact located
  · intro entry member cycle
    cases selected with
    | selected safe unique clear =>
        exact safe.2.2.1 (Or.inr ⟨plan,frame.key_eq.symm ▸ frame,entry,member,cycle⟩)

theorem selected_alternatives (selected : Local registry state input.occurrence (.selected key children)) :
    AlternativesSafe registry state input := by
  intro plan same frame
  exact selected_safe selected frame

def Extension (state : State roles) (effect : Effect roles) : Prop :=
  GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet ∧
    ∃ model, InstallationModels state effect model

theorem selected_installable_iff
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (selected : Local registry state effect.plan.packet.site.occurrence
      (.selected effect.plan.packet.declaration.id children))
    (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core) :
    Installable registry state effect ↔ Extension state effect := by
  constructor
  · exact fun enabled => ⟨enabled.choice,enabled.common⟩
  · rintro ⟨choice,common⟩
    have frame := snapshot ▸ registryEq ▸ effect.frame
    have positions := selected_safe selected frame
    have alternatives := selected_alternatives (effect.plan.input_exact.symm ▸ selected)
    cases selected with
    | selected safe unique clear =>
        exact ⟨registryEq,snapshot,safe,GeneralNominalCenteredHeadMatStepBoundary.reachable_cache reachable,
          GeneralNominalCenteredHeadMatStepTrace.emitted_complete reachable frame,choice,positions,alternatives,common⟩

theorem enabled_or_committed (enabled : Installable registry state effect)
    (generated : GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence) :
    Committed state effect.plan ∨ ∃ after, Step registry root state after := by
  classical
  by_cases done : Committed state effect.plan
  · exact Or.inl done
  · exact Or.inr ⟨install state effect,effect.plan.packet.site.occurrence,generated,.install effect enabled done⟩

theorem stable_selected_committed
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (stable : Stable registry state root)
    (generated : GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence)
    (selected : Local registry state effect.plan.packet.site.occurrence (.selected effect.plan.packet.declaration.id children))
    (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core)
    (extension : Extension state effect) : Committed state effect.plan := by
  obtain done | ⟨after,focus,generated,action⟩ := enabled_or_committed
    ((selected_installable_iff reachable selected registryEq snapshot).mpr extension) generated
  · exact done
  · exact False.elim (stable focus generated after action)

theorem chosen_effects (selected : Local registry state focus (.selected key children))
    (baseline : ∃ model, Models state model ∧ GeneralNominalCenteredHeadMatStepLocal.ChosenHead registry state focus key model) :
    ∃ model, Models state model ∧ GeneralNominalCenteredHeadMatStepLocal.ChosenEffects registry state focus key model := by
  classical
  apply Classical.byContradiction
  exact fun absent => B4TargetV6.selected_clear selected ⟨baseline,absent⟩

theorem stable_focus_selected_committed
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (stable : Stable registry state effect.plan.packet.site.occurrence)
    (selected : Local registry state effect.plan.packet.site.occurrence (.selected effect.plan.packet.declaration.id children))
    (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core)
    (extension : Extension state effect) : Committed state effect.plan := by
  classical
  apply Classical.byContradiction
  intro absent
  exact stable _ .root _ (.install effect
    ((selected_installable_iff reachable selected registryEq snapshot).mpr extension) absent)

end Yulang.GeneralNominalCenteredHeadMatStepAvailability
