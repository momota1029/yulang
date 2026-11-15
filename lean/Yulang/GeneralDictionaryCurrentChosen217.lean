import Yulang.GeneralDictionaryCurrentHeadEquations217
import Yulang.GeneralDictionaryDefaultAvailability208
import Yulang.GeneralNominalCenteredHeadMatStepCompletion

namespace Yulang.GeneralDictionaryCurrentChosen217
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultBoundary208 (boundary Local)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryCountedProjection216 (Agreement)
variable {roles : Roles.RoleDecls} {state : State roles}
set_option backward.isDefEq.respectTransparency false

theorem chosen_of_obstructions
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (selected : Local value state focus (.selected key children))
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key candidate)
    (model : Assignment) (valid : Models state model) (agreement : Agreement candidate model)
    (overlap : GeneralDictionaryMixedMerge216.Overlap candidate.packet.context.state candidate.packet.registry
      candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings
      (GeneralDictionaryCurrentCompletion216.support state candidate) model) :
    ∃ extended, Models state extended ∧
      GeneralNominalCenteredHeadMatStepLocal.ChosenHead (registry value) state focus key extended := by
  have ready := GeneralDictionaryDefaultAvailability208.ready checked reachable frame
  obtain ⟨start,initial,path⟩ := reachable
  obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ :=
    GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
  obtain ⟨extended,journal,_,head⟩ := GeneralDictionaryCurrentHeadEquations217.common_head
    (GeneralNominalCenteredHeadAllocBoundary.checked_compiled checked).2
    source point ground coverage path candidate frame model valid agreement overlap
  have prior := GeneralDictionaryDefaultAvailability208.selected_prior selected
  cases prior with
  | selected safe unique clear => exact ⟨extended,journal,⟨children,unique⟩,candidate,frame,ready,head⟩

theorem effect_of_obstructions
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (selected : Local value state focus (.selected key children))
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key candidate)
    (model : Assignment) (valid : Models state model) (agreement : Agreement candidate model)
    (overlap : GeneralDictionaryMixedMerge216.Overlap candidate.packet.context.state candidate.packet.registry
      candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings
      (GeneralDictionaryCurrentCompletion216.support state candidate) model) :
    ∃ (effect : Effect roles) (extended : Assignment), effect.registry = registry value ∧ effect.snapshot = state.core ∧
      effect.plan.packet.site.occurrence = focus ∧ effect.plan.packet.declaration.id = key ∧
      effect.plan.packet.children = children ∧ Models state extended ∧ effect.Holds extended := by
  exact GeneralNominalCenteredHeadMatStepCompletion.selected_effect_model
    (GeneralDictionaryDefaultAvailability208.selected_prior selected)
    (chosen_of_obstructions checked reachable selected candidate frame model valid agreement overlap)
end Yulang.GeneralDictionaryCurrentChosen217
