import Yulang.GeneralNominalCenteredHeadMatCompletionRequests

set_option backward.isDefEq.respectTransparency false

/-! Every post-install live effect follows from its current class equations.
The remaining common-model problem consists of the current journal, corrected
packet, and chosen class effects, without extra future live-ledger premises. -/
namespace Yulang.GeneralNominalCenteredHeadMatCompletionLive
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatStepHistory (Built)
open GeneralNominalCenteredHeadMatCompletionRequests
open GeneralNominalCenteredHeadMatStepBoundary (boundary)
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}

theorem effect_present (built : Built registry context root state) (member : effect ∈ state.effects) :
    Present state.core effect.plan.packet.site.occurrence.identity := by
  induction built with
  | initial => cases member
  | install _ installed snapshot _ ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨effect.plan.packet.site,List.mem_append_left _
          (snapshot ▸ effect.frame.raw_recorded),rfl⟩
      · obtain ⟨site,present,same⟩ := ih member
        exact ⟨site,List.mem_append_left _ present,same⟩
  | merge _ _ _ _ ih => exact ih member
  | context _ _ _ _ ih => exact ih member

theorem class_effects_install (checked : Checked registry) (built : Built registry context root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core plan.packet.site.occurrence plan.packet.declaration.id plan)
    (present : Present state.core focus.identity) (other : Plan roles) (model) :
    GeneralNominalCenteredHeadMatEffects.ClassEffects (installCore state.core plan) focus other model ↔
      GeneralNominalCenteredHeadMatEffects.ClassEffects state.core focus other model := by
  simp only [GeneralNominalCenteredHeadMatEffects.ClassEffects,GeneralNominalCenteredHeadOutputs.EqualOutputs,
    install_requests checked (invariant built) frame present]

theorem installation_models_iff (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core) (model) :
    InstallationModels state effect model ↔ Models state model ∧
      GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model := by
  constructor
  · exact fun valid => ⟨valid.1,valid.2.1,valid.2.2.1⟩
  · rintro ⟨valid,branch,chosen⟩
    obtain ⟨start,⟨context,labels,source,point,ground,coverage,rfl⟩,path⟩ := reachable
    have built := GeneralNominalCenteredHeadMatStepTrace.built_trace path
    have frame := snapshot ▸ registryEq ▸ effect.frame
    refine ⟨valid,branch,chosen,?_,?_⟩
    · exact (class_effects_install checked built frame
        ⟨effect.plan.packet.site,frame.raw_recorded,rfl⟩ effect.plan model).mpr (snapshot ▸ chosen.2)
    · intro prior member
      exact (class_effects_install checked built frame (effect_present built member) prior.plan model).mpr
        (valid.2.2.2.2.2 prior member).2

theorem extension_iff (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core) :
    GeneralNominalCenteredHeadMatStepAvailability.Extension state effect ↔
      GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet ∧
        ∃ model, Models state model ∧ GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model := by
  unfold GeneralNominalCenteredHeadMatStepAvailability.Extension
  exact and_congr Iff.rfl (exists_congr (installation_models_iff checked reachable registryEq snapshot))

theorem common_successor_model (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core)
    (valid : Models state model) (branch : GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model)
    (chosen : effect.Holds model) : Models (install state effect) model :=
  (install_models snapshot).mpr ((installation_models_iff checked reachable registryEq snapshot model).mpr ⟨valid,branch,chosen⟩)

theorem selected_installable_iff (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (selected : GeneralNominalCenteredHeadMatStepBoundary.Local registry state effect.plan.packet.site.occurrence
      (.selected effect.plan.packet.declaration.id children))
    (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core) :
    GeneralNominalCenteredHeadMatStepKernel.Installable registry state effect ↔
      GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet ∧
        ∃ model, Models state model ∧ GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model :=
  (GeneralNominalCenteredHeadMatStepAvailability.selected_installable_iff reachable selected registryEq snapshot).trans
    (extension_iff checked reachable registryEq snapshot)

end Yulang.GeneralNominalCenteredHeadMatCompletionLive
