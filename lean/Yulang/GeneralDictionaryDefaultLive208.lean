import Yulang.GeneralDictionaryDefaultBoundary208
import Yulang.GeneralDictionaryDefaultTrace208
import Yulang.GeneralNominalCenteredHeadMatCompletionLive

set_option backward.isDefEq.respectTransparency false

/-! Live-ledger common-model reduction for the corrected reachable states.
It does not posit that every selected demand has a common model. -/
namespace Yulang.GeneralDictionaryDefaultLive208
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatCompletionLive (class_effects_install effect_present)
open GeneralDictionaryDefaultBoundary208 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}

theorem installation_models_iff (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (registryEq : effect.registry = registry value) (snapshot : effect.snapshot = state.core) (model) :
    InstallationModels state effect model ↔ Models state model ∧
      GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model := by
  constructor
  · exact fun valid => ⟨valid.1,valid.2.1,valid.2.2.1⟩
  · rintro ⟨valid,branch,chosen⟩
    obtain ⟨start,initial,path⟩ := reachable
    have compiled := GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
    obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ := compiled
    have checked := (GeneralNominalCenteredHeadAllocBoundary.checked_compiled checked).2
    have built := GeneralDictionaryDefaultTrace208.built_trace path
    have frame := snapshot ▸ registryEq ▸ effect.frame
    refine ⟨valid,branch,chosen,?_,?_⟩
    · exact (class_effects_install checked built frame
        ⟨effect.plan.packet.site,frame.raw_recorded,rfl⟩ effect.plan model).mpr (snapshot ▸ chosen.2)
    · intro prior member
      exact (class_effects_install checked built frame (effect_present built member) prior.plan model).mpr
        (valid.2.2.2.2.2 prior member).2

theorem extension_iff (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (registryEq : effect.registry = registry value) (snapshot : effect.snapshot = state.core) :
    GeneralNominalCenteredHeadMatStepAvailability.Extension state effect ↔
      GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet ∧
        ∃ model, Models state model ∧ GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model := by
  unfold GeneralNominalCenteredHeadMatStepAvailability.Extension
  exact and_congr Iff.rfl (exists_congr (installation_models_iff checked reachable registryEq snapshot))

theorem common_successor_model (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (registryEq : effect.registry = registry value) (snapshot : effect.snapshot = state.core)
    (valid : Models state model) (branch : GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model)
    (chosen : effect.Holds model) : Models (install state effect) model :=
  (install_models snapshot).mpr ((installation_models_iff checked reachable registryEq snapshot model).mpr ⟨valid,branch,chosen⟩)

end Yulang.GeneralDictionaryDefaultLive208
