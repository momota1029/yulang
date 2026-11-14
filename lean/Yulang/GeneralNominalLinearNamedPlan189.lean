import Yulang.GeneralNominalLinearVariableModels189

/-! Named-output leaf installation for finite distinct-name variable heads.
Every witness uses the same assignment for current, private, and named models. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalLinearNamedPlan189
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadOutputs
open GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalSingleVariableModels189 (leaf_named_schema actual_schema_raw installed_outputs)
variable {roles : Roles.RoleDecls}

private theorem linear_report (state : GeneralNominalState.State)
    (entries : List (Nat × Fin state.base.slots)) (index : Nat) :
    inspectMany state (entries.map fun entry => .variables [entry.1])
      (entries.map fun entry => (entry.2,entry.2)) (fun _ => none) index =
    { captures := entries.map (fun entry => ⟨entry.1,(entry.2,entry.2),none⟩),
      checked := entries.map (fun entry => (entry.2,entry.2)) } := by
  induction entries generalizing index with
  | nil => simp [inspectMany]
  | cons head tail ih =>
      simp [inspectMany,inspect,Report.append,ih]

theorem named_plan (candidate : Plan roles) (entries : List (Nat × Fin candidate.packet.context.state.base.slots))
    (unique : (entries.map Prod.fst).Nodup)
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = entries.map fun entry => .variables [entry.1])
    (bounds : candidate.packet.bounds = entries.map fun entry => (entry.2,entry.2))
    (names : candidate.packet.declaration.inputNames = entries.map Prod.fst)
    (leaf : candidate.packet.declaration.requirements = [])
    (model : Assignment) (valid : GeneralNominalState.Models candidate.packet.context.state model)
    (head : HeadEquations candidate model)
    (outputs : candidate.SchemaHolds (GeneralNominalPacketSupport.namedSchema candidate.packet) model) :
    candidate.Holds model := by
  have actual : GeneralDictionaryActualSchema.ActualOnly (GeneralNominalPacketSupport.namedSchema candidate.packet) := by
    rw [leaf_named_schema candidate leaf]
    exact GeneralDictionaryActualSchema.root_generated_actual candidate.packet.context.state candidate.packet.context.interpretation candidate.packet.declaration candidate.packet.site.occurrence
  have scope : ∀ entry ∈ (GeneralNominalPacketSupport.namedSchema candidate.packet).variables,
      entry.name ∈ candidate.packet.declaration.inputNames ∨ entry.name ∈ candidate.packet.declaration.outputNames := by
    rw [leaf_named_schema candidate leaf]
    exact GeneralDictionaryActualSchemaScope.root_generated_scoped _ _ _ _ candidate.packet.checked.scope
  have origins : ∀ captured ∈ (GeneralNominalPacketSupport.report candidate.packet).captures, captured.origin = none := by
    intro captured member
    have report := linear_report candidate.packet.context.state entries 0
    simp only [GeneralNominalPacketSupport.report,GeneralNominalRecursiveCandidates.report,
      query,bounds,report] at member
    obtain ⟨entry,_,rfl⟩ := List.mem_map.mp member
    rfl
  have raw := actual_schema_raw candidate _ model outputs actual scope head.2.1 origins
  have branch := GeneralNominalLinearVariableModels189.head_models candidate entries unique query bounds names model valid
  refine ⟨⟨branch.1,branch.2,raw⟩,head.1,?_,head.2.2,?_,outputs,?_⟩
  · intro used member
    rcases member with member | needed
    · exact head.2.1 used member
    · simp [GeneralNominalSharedCaptures.Needed,leaf] at needed
  · rw [GeneralNominalHeadLeafPlan189.input_schema_empty candidate leaf]
    simp [Plan.SchemaHolds]
  · simp [leaf]

/-- Nonempty named requests are allowed. The returned assignment satisfies
both the actual full plan and its named-output equations, without substitution. -/
theorem selected_named_plan
    {registry : Registry} {root : Occurrence roles} {state : State roles}
    (checked : Checked registry)
    (source : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry root state)
    (selected : GeneralNominalCenteredHeadWFBoundary.Local registry state root (.selected key children))
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (entries : List (Nat × Fin candidate.packet.context.state.base.slots))
    (unique : (entries.map Prod.fst).Nodup)
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = entries.map fun entry => .variables [entry.1])
    (bounds : candidate.packet.bounds = entries.map fun entry => (entry.2,entry.2))
    (names : candidate.packet.declaration.inputNames = entries.map Prod.fst)
    (leaf : candidate.packet.declaration.requirements = [])
    (ready : EffectsReady state.core root candidate) :
    ∃ model, Models state model ∧ candidate.Holds model ∧
      OutputEquations state.core root candidate model := by
  obtain ⟨model,valid,head,outputs⟩ :=
    GeneralNominalInitialFrameUnique189.selected_frame_model checked state source selected candidate frame ready
  have requestEq : requests state.core root = root.demand.outputs := by
    obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
    subst state
    exact GeneralNominalHeadInitialEffects188.initial_requests context
  have schemaEq : GeneralNominalPacketSupport.namedSchema candidate.packet = outputSchema state.core root candidate := by
    rw [leaf_named_schema candidate leaf]
    simp only [outputSchema,requestEq,Plan.schema,GeneralNominalMaterialization.rootRequests,frame.occurrence_eq]
  refine ⟨model,valid,named_plan candidate entries unique query bounds names leaf model ?_ head ?_,outputs⟩
  · rw [frame.context_eq]
    exact valid.1.1.1
  · rw [schemaEq]
    exact outputs.1

theorem selected_named_installable
    {registry : Registry} {root : Occurrence roles} {state : State roles}
    (checked : Checked registry)
    (source : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry root state)
    (selected : GeneralNominalCenteredHeadWFBoundary.Local registry state root (.selected key children))
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (entries : List (Nat × Fin candidate.packet.context.state.base.slots))
    (unique : (entries.map Prod.fst).Nodup)
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = entries.map fun entry => .variables [entry.1])
    (bounds : candidate.packet.bounds = entries.map fun entry => (entry.2,entry.2))
    (names : candidate.packet.declaration.inputNames = entries.map Prod.fst)
    (leaf : candidate.packet.declaration.requirements = [])
    (ready : EffectsReady state.core root candidate) :
    ∃ support, GeneralNominalCenteredHeadStepKernel.Installable registry state candidate support := by
  obtain ⟨model,valid,holds,outputs⟩ := selected_named_plan checked source selected candidate frame entries unique
    query bounds names leaf ready
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


end Yulang.GeneralNominalLinearNamedPlan189
