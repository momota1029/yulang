import Yulang.GeneralNominalInitialOutputExact189

/-! A linear single-variable head does not introduce merged capture names.
Its private raw constraints hold in every current model at a point argument.
This same-assignment result does not extend to repeated capture merges. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalSingleVariableModels189
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadOutputs
open GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls}

theorem head_models (candidate : Plan roles) (slot : Fin candidate.packet.context.state.base.slots)
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = [.variables [name]])
    (bounds : candidate.packet.bounds = [(slot,slot)])
    (names : candidate.packet.declaration.inputNames = [name])
    (model : Assignment) (valid : GeneralNominalState.Models candidate.packet.context.state model) :
    GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model := by
  have reportEq : GeneralNominalPacketSupport.report candidate.packet =
      ({ captures := [⟨name,(slot,slot),none⟩], checked := [(slot,slot),(slot,slot)] } : Report candidate.packet.context.state) := by
    simp [GeneralNominalPacketSupport.report,GeneralNominalRecursiveCandidates.report,query,bounds,
      inspectMany,inspect,Report.append]
  have bindingsEq : candidate.packet.bindings = [(name,candidate.packet.context.state.base.source slot,
      candidate.packet.context.state.base.source slot)] := by
    change bindings _ (GeneralNominalPacketSupport.report candidate.packet) = _
    rw [reportEq]
    rfl
  rw [GeneralNominalHeadBranchFrame187.head_models_exact,GeneralNominalPacketSupport.private_exact]
  refine ⟨⟨valid,?_,?_,?_⟩,?_⟩
  · rw [bindingsEq]
    intro first one last two same
    simp only [List.mem_singleton] at one two
    subst first; subst last
    exact subtype_refl _
  · simp [GeneralNominalAllocation.merges,names,bindingsEq,GeneralNominalAllocation.occurrences,
      PresenceNormalForm.All]
  · rw [reportEq]
    simp only [selfChecks,List.map_cons,List.map_nil,PresenceNormalForm.All,List.mem_cons,List.not_mem_nil,or_false,or_self]
    intro atom member
    rcases member with rfl | rfl <;> exact subtype_refl _
  · rw [reportEq]
    simp [ProjectionModels]

/-- The named-output witness's assignment also satisfies the actual private
head, with no extension or model substitution, for this linear fragment. -/
theorem selected_named_head_model
    {registry : Registry} {root : Occurrence roles} {state : State roles}
    (checked : Checked registry)
    (source : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry root state)
    (selected : GeneralNominalCenteredHeadWFBoundary.Local registry state root (.selected key children))
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (slot : Fin candidate.packet.context.state.base.slots)
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = [.variables [name]])
    (bounds : candidate.packet.bounds = [(slot,slot)])
    (names : candidate.packet.declaration.inputNames = [name])
    (ready : EffectsReady state.core root candidate) :
    ∃ model, Models state model ∧ HeadEquations candidate model ∧
      OutputEquations state.core root candidate model ∧
      GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model := by
  obtain ⟨model,valid,head,outputs⟩ :=
    GeneralNominalInitialFrameUnique189.selected_frame_model checked state source selected candidate frame ready
  refine ⟨model,valid,head,outputs,head_models candidate slot query bounds names model ?_⟩
  rw [frame.context_eq]
  exact valid.1.1.1

theorem actual_schema_raw (candidate : Plan roles) (body : GeneralNominalMaterialization.Schema)
    (model : Assignment) (centered : candidate.SchemaHolds body model)
    (actual : GeneralDictionaryActualSchema.ActualOnly body)
    (scope : ∀ entry ∈ body.variables, entry.name ∈ candidate.packet.declaration.inputNames ∨
      entry.name ∈ candidate.packet.declaration.outputNames)
    (fits : ∀ name ∈ candidate.packet.declaration.inputNames, GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs name) (model (candidate.binder name)).1)
    (origins : ∀ captured ∈ (GeneralNominalPacketSupport.report candidate.packet).captures,
      captured.origin = none) :
    GeneralNominalMaterialization.Models candidate.packet.context.state candidate.packet.declaration
      (GeneralNominalPacketSupport.capture candidate.packet) (GeneralNominalPacketSupport.report candidate.packet)
      body model := by
  have same (entry : GeneralNominalMaterialization.Use) (member : entry ∈ body.variables) : GeneralNominalOriginTerms.Same model entry.origin (.source (candidate.binder entry.name)) := by
    simpa only [actual entry member,ite_true] using centered.2 entry member
  refine ⟨centered.1,?_,?_,?_⟩
  · intro entry member
    refine ⟨(same entry member).1,?_⟩
    intro value seen
    have equal := (same entry member).2.2 value _ seen (.source _)
    unfold GeneralNominalMaterialization.VariableHolds
    by_cases output : entry.name ∈ candidate.packet.declaration.outputNames
    · simpa only [output,ite_true,Plan.binder] using equal
    · simp only [output,ite_false,actual entry member]
      have fit := fits entry.name ((scope entry member).resolve_right output)
      exact ⟨subtype_trans fit.1 equal.2,subtype_trans equal.1 fit.2⟩
  · intro first one last two equal _ _ x y seenX seenY
    have a := (same first one).2.2 x _ seenX (.source _)
    have b := (same last two).2.2 y _ seenY (.source _)
    rw [equal] at a
    exact ⟨subtype_trans a.1 b.2,subtype_trans b.1 a.2⟩
  · intro entry member captured present equal mode origin found
    rw [origins captured present] at found
    cases found

theorem leaf_named_schema (candidate : Plan roles) (leaf : candidate.packet.declaration.requirements = []) :
    GeneralNominalPacketSupport.namedSchema candidate.packet =
      GeneralNominalMaterialization.generated candidate.packet.context.state candidate.packet.context.interpretation
        (GeneralNominalMaterialization.rootRequests candidate.packet.declaration candidate.packet.site.occurrence) := by
  unfold GeneralNominalPacketSupport.namedSchema GeneralNominalRecursiveCandidates.generated
    GeneralNominalMaterialization.requests
  rw [GeneralNominalHeadLeafPlan189.emitted_empty candidate leaf]
  simp

theorem named_plan (candidate : Plan roles) (slot : Fin candidate.packet.context.state.base.slots)
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = [.variables [name]])
    (bounds : candidate.packet.bounds = [(slot,slot)])
    (names : candidate.packet.declaration.inputNames = [name])
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
    simp [GeneralNominalPacketSupport.report,GeneralNominalRecursiveCandidates.report,query,bounds,
      inspectMany,inspect,Report.append]
  have raw := actual_schema_raw candidate _ model outputs actual scope head.2.1 origins
  have branch := head_models candidate slot query bounds names model valid
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
    (slot : Fin candidate.packet.context.state.base.slots)
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = [.variables [name]])
    (bounds : candidate.packet.bounds = [(slot,slot)])
    (names : candidate.packet.declaration.inputNames = [name])
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
  refine ⟨model,valid,named_plan candidate slot query bounds names leaf model ?_ head ?_,outputs⟩
  · rw [frame.context_eq]
    exact valid.1.1.1
  · rw [schemaEq]
    exact outputs.1

theorem installed_outputs {model : Assignment} (candidate : Plan roles) (leaf : candidate.packet.declaration.requirements = [])
    (before : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles) (support : List (Occurrence roles))
    (outputs : OutputEquations before root candidate model) :
    OutputEquations (GeneralNominalCenteredSteps.install before candidate support) root candidate model := by
  apply GeneralNominalCenteredHeadStepEffects.output_equations_restrict _ outputs
  apply GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
  · have sites : (GeneralNominalCenteredSteps.install before candidate support).erased.current.sites =
        before.erased.current.sites := by
      simp [GeneralNominalCenteredSteps.install,GeneralNominalSharedSteps.install,
        GeneralNominalFeedbackSites.install,GeneralNominalSharedEmission.emitted,
        GeneralNominalHeadLeafPlan189.children_empty candidate leaf]
    rw [sites]
    exact fun _ member => member
  · exact fun _ member => member

theorem selected_named_installable
    {registry : Registry} {root : Occurrence roles} {state : State roles}
    (checked : Checked registry)
    (source : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry root state)
    (selected : GeneralNominalCenteredHeadWFBoundary.Local registry state root (.selected key children))
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (slot : Fin candidate.packet.context.state.base.slots)
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = [.variables [name]])
    (bounds : candidate.packet.bounds = [(slot,slot)])
    (names : candidate.packet.declaration.inputNames = [name])
    (leaf : candidate.packet.declaration.requirements = [])
    (ready : EffectsReady state.core root candidate) :
    ∃ support, GeneralNominalCenteredHeadStepKernel.Installable registry state candidate support := by
  obtain ⟨model,valid,holds,outputs⟩ := selected_named_plan checked source selected candidate frame slot
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

end Yulang.GeneralNominalSingleVariableModels189
