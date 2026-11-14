import Yulang.GeneralNominalLinearNamedPlan189

/-! A positive full leaf-plan/current/output witness supplies the remaining
operational installation fields at an initial selected source. The witness is
explicit; this theorem does not infer common satisfiability from two models. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalLeafWitnessInstall190
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadOutputs
open GeneralNominalSingleVariableModels189 (leaf_named_schema installed_outputs)
variable {roles : Roles.RoleDecls}

theorem installable_of_named_witness
    {registry : Registry} {root : Occurrence roles} {state : State roles}
    (source : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry root state)
    (selected : GeneralNominalCenteredHeadWFBoundary.Local registry state root (.selected key children))
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (leaf : candidate.packet.declaration.requirements = [])
    (ready : EffectsReady state.core root candidate)
    (witness : ∃ model, Models state model ∧ candidate.Holds model ∧
      OutputEquations state.core root candidate model) :
    ∃ support, GeneralNominalCenteredHeadStepKernel.Installable registry state candidate support := by
  obtain ⟨model,valid,holds,outputs⟩ := witness
  have requestEq : requests state.core root = root.demand.outputs := by
    obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
    subst state
    exact GeneralNominalHeadInitialEffects188.initial_requests context
  have schemaEq : GeneralNominalPacketSupport.namedSchema candidate.packet = outputSchema state.core root candidate := by
    rw [leaf_named_schema candidate leaf]
    simp only [outputSchema,requestEq,Plan.schema,GeneralNominalMaterialization.rootRequests,frame.occurrence_eq]
  have old := GeneralNominalCenteredHeadWFBoundary.local_iff.mp selected
  have localPlan : GeneralNominalCenteredHeadStepBoundary.Local registry state candidate.packet.site.occurrence
      (.selected candidate.packet.declaration.id children) := by
    simpa only [frame.occurrence_eq,frame.key_eq] using old
  have framePlan : Frame registry state.core candidate.packet.site.occurrence candidate.packet.declaration.id candidate := by
    simpa only [frame.occurrence_eq,frame.key_eq] using frame
  apply (GeneralNominalCenteredHeadStepAvailability.selected_installable_iff localPlan framePlan
    (by simpa only [frame.occurrence_eq] using ready)).mpr
  refine ⟨?_,?_,[],?_,model,valid,holds,?_,?_,?_⟩
  · change (GeneralNominalPacketSupport.namedSchema candidate.packet).unknown = false
    rw [schemaEq]
    exact ready.2
  · obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
    subst state
    simp [GeneralNominalCycleSteps.ChoiceCompatible,initial,GeneralNominalCenteredSteps.initial,
      GeneralNominalCenteredSteps.initialAt,GeneralNominalSupport.initial,GeneralNominalSaturationState.initial]
  · apply (GeneralNominalCenteredHeadStepAvailability.frame_value_iff framePlan []).mp
    obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
    subst state
    exact GeneralNominalCenteredHeadStepAvailability.selected_initial_value old frame
  · simpa only [frame.occurrence_eq] using outputs
  · simpa only [frame.occurrence_eq] using installed_outputs candidate leaf state.core root [] outputs
  · obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
    subst state
    simp [initial]

end Yulang.GeneralNominalLeafWitnessInstall190
