import Yulang.GeneralDictionaryDefaultCache208
import Yulang.GeneralDictionaryDefaultLive208
import Yulang.GeneralDictionaryDefaultCommitment208

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryDefaultAvailability208
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultBoundary208 (boundary Local)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}

theorem selected_prior
    (selected : Local value state focus (.selected key children)) :
    GeneralNominalCenteredHeadMatStepBoundary.Local (registry value) state focus (.selected key children) := by
  have compiled := GeneralNominalCenteredHeadAllocV7Boundary.local_iff.mp
    (GeneralDictionaryDefaultBoundary208.local_iff.mp selected)
  exact (B4TargetV7.selected_iff.mp compiled).1

theorem reachable_cache (reachable : B4TargetV7.Reachable (boundary roles) value root state) :
    GeneralNominalCenteredHeadMatStepCache.Valid state := by
  obtain ⟨start,initial,path⟩ := reachable
  have compiled := GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
  obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ := compiled
  exact GeneralDictionaryDefaultCache208.steps_cache path
    (GeneralDictionaryDefaultCache208.initial_valid context root)

theorem ready (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key plan) :
    GeneralNominalCenteredHeadMatEffects.Ready state.core focus plan := by
  obtain ⟨start,initial,path⟩ := reachable
  have compiled := GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
  obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ := compiled
  exact GeneralNominalCenteredHeadMatStepHistory.ready
    (GeneralNominalCenteredHeadAllocBoundary.checked_compiled checked).2
    source.roles_agree coverage (GeneralDictionaryDefaultTrace208.built_trace path) frame

theorem emitted_complete (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key plan) :
    (GeneralNominalCenteredHeadMatPlans.emittedSchema plan).unknown = false := by
  obtain ⟨start,initial,path⟩ := reachable
  have compiled := GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
  obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ := compiled
  exact GeneralNominalCenteredHeadMatStepHistory.emitted_complete coverage
    (GeneralDictionaryDefaultTrace208.built_trace path) frame

/-- A genuine extension is exactly compatibility plus one joint model.
This does not infer such a model from selection alone. -/
theorem selected_installable_iff (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (selected : Local value state effect.plan.packet.site.occurrence
      (.selected effect.plan.packet.declaration.id children))
    (registryEq : effect.registry = registry value) (snapshot : effect.snapshot = state.core) :
    GeneralDictionaryDefaultKernel208.Installable (registry value) state effect ↔
      GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet ∧
        ∃ model, Models state model ∧ GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model := by
  rw [← GeneralDictionaryDefaultLive208.extension_iff checked reachable registryEq snapshot]
  constructor
  · exact fun enabled => ⟨enabled.choice,enabled.common⟩
  · rintro ⟨choice,common⟩
    have frame := snapshot ▸ registryEq ▸ effect.frame
    have prior := selected_prior selected
    have positions := GeneralNominalCenteredHeadMatStepAvailability.selected_safe prior frame
    have alternatives := GeneralNominalCenteredHeadMatStepAvailability.selected_alternatives
      (effect.plan.input_exact.symm ▸ prior)
    cases prior with
    | selected safe unique clear =>
      exact ⟨registryEq,snapshot,safe,reachable_cache reachable,
        emitted_complete reachable frame,choice,positions,alternatives,common⟩

theorem selected_frame
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (selected : Local value state focus (.selected key children)) :
    ∃ plan, GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key plan ∧ plan.packet.children = children := by
  have prior := selected_prior selected
  obtain ⟨center,recorded,centerEq⟩ := (GeneralNominalCenteredHeadMatStepBoundary.selected_ready prior).1
  obtain ⟨first,initial,path⟩ := reachable
  have compiled := GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
  obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ := compiled
  obtain ⟨raw,rawRecorded,rawEq⟩ := GeneralDictionaryDefaultTrace208.centered_registered path center recorded
  have rawFocus := rawEq.trans centerEq
  cases prior with
  | selected safe unique clear =>
      obtain ⟨known,declaration,visible,checked,keyEq,role,bounds,located,prepared,childrenEq⟩ := unique.1
      let packet : GeneralNominalSaturationState.Packet roles :=
        ⟨registry value,state.core.erased.current.context,raw,declaration,checked,bounds⟩
      let plan : Plan roles := ⟨packet,center,rawEq.symm⟩
      refine ⟨plan,⟨rfl,rfl,rawFocus,keyEq,rawRecorded,recorded,visible,role,located,prepared⟩,?_⟩
      change GeneralNominalAllocation.children _ (registry value) raw.occurrence declaration checked _ = _
      rw [rawFocus,childrenEq]
      rfl

theorem selected_effect (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (selected : Local value state focus (.selected key children)) :
    ∃ effect : Effect roles, effect.registry = registry value ∧ effect.snapshot = state.core ∧
      effect.plan.packet.site.occurrence = focus ∧ effect.plan.packet.declaration.id = key ∧
      effect.plan.packet.children = children := by
  obtain ⟨plan,frame,kids⟩ := selected_frame reachable selected
  have ready := ready checked reachable frame
  have prior := selected_prior selected
  cases prior with
  | selected safe unique clear =>
      have unique' : GeneralNominalCenteredHeadCandidates.Unique (registry value) state.core.erased.current.context
          plan.packet.site.occurrence plan.packet.declaration.id plan.packet.children :=
        frame.occurrence_eq.symm ▸ frame.key_eq.symm ▸ kids.symm ▸ unique
      let effect : Effect roles := ⟨registry value,state.core,plan,
        frame.occurrence_eq.symm ▸ frame.key_eq.symm ▸ frame,unique',frame.occurrence_eq.symm ▸ ready⟩
      exact ⟨effect,rfl,rfl,frame.occurrence_eq,frame.key_eq,kids⟩

end Yulang.GeneralDictionaryDefaultAvailability208
