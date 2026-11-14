import Yulang.GeneralNominalHeadRecursiveExtension188

set_option backward.isDefEq.respectTransparency false

/-! Leaf declarations without named requests turn genuine head feasibility into
full centered packet feasibility. Recursive head queries remain unrestricted. -/
namespace Yulang.GeneralNominalHeadLeafPlan189
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
variable {state : State roles}

theorem emitted_empty (plan : Plan roles) (leaf : plan.packet.declaration.requirements = [])
    (capture : GeneralDeclarationDemands.Capture)
    (allocate : (clause : Clause) → GeneralDeclarationDemands.Allocation roles clause) :
    GeneralCanonicalChildOrder.canonicalEmit plan.packet.site.occurrence.identity
      plan.packet.declaration plan.packet.checked capture allocate = [] := by
  apply List.Perm.eq_nil
  exact (GeneralCanonicalChildOrder.canonicalEmit_perm ..).symm.trans
    (by simp [GeneralDeclarationDemands.emitAll,leaf])

theorem input_schema_empty (plan : Plan roles) (leaf : plan.packet.declaration.requirements = []) :
    GeneralNominalPacketSupport.inputSchema plan.packet = {} := by
  simp [GeneralNominalPacketSupport.inputSchema,GeneralNominalPacketSupport.inputRequests,
    emitted_empty plan leaf,GeneralNominalMaterialization.generated]

theorem named_schema_empty (plan : Plan roles) (leaf : plan.packet.declaration.requirements = [])
    (empty : plan.packet.site.occurrence.demand.outputs = []) :
    GeneralNominalPacketSupport.namedSchema plan.packet = {} := by
  simp [GeneralNominalPacketSupport.namedSchema,GeneralNominalRecursiveCandidates.generated,
    GeneralNominalMaterialization.requests,GeneralNominalMaterialization.rootRequests,empty,
    GeneralNominalMaterialization.generated]
  rw [emitted_empty plan leaf]
  rfl

theorem head_to_plan (plan : Plan roles) (leaf : plan.packet.declaration.requirements = [])
    (empty : plan.packet.site.occurrence.demand.outputs = []) (model : Assignment)
    (head : HeadEquations plan model)
    (branch : GeneralNominalCenteredHeadCandidates.HeadModels plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds model) :
    plan.Holds model := by
  constructor
  · change _ ∧ _ ∧ _
    refine ⟨branch.1,branch.2,?_⟩
    change GeneralNominalMaterialization.Models _ _ _ _ (GeneralNominalPacketSupport.namedSchema plan.packet) model
    rw [named_schema_empty plan leaf empty]
    exact GeneralNominalMaterialization.empty_models ..
  · refine ⟨head.1,?_,head.2.2,?_,?_,?_⟩
    · intro name member
      rcases member with member | needed
      · exact head.2.1 name member
      · simp [GeneralNominalSharedCaptures.Needed,leaf] at needed
    · rw [input_schema_empty plan leaf]
      simp [Plan.SchemaHolds]
    · rw [named_schema_empty plan leaf empty]
      simp [Plan.SchemaHolds]
    · simp [leaf]

theorem initial_plan (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (leaf : candidate.packet.declaration.requirements = []) (empty : root.demand.outputs = []) :
    ∃ model, Models state model ∧ candidate.Holds model := by
  obtain ⟨model,current,head,branch,_⟩ :=
    GeneralNominalHeadRecursiveExtension188.initial_extension checked source candidate frame
  exact ⟨model,current,head_to_plan candidate leaf (frame.occurrence_eq ▸ empty) model head branch⟩

theorem children_empty (plan : Plan roles) (leaf : plan.packet.declaration.requirements = []) :
    plan.packet.children = [] := by
  unfold GeneralNominalSaturationState.Packet.children GeneralNominalAllocation.children
    GeneralDictionaryEmissionPlans.children
  rw [emitted_empty plan leaf]
  rfl

theorem installed_requests_empty (plan : Plan roles)
    (leaf : plan.packet.declaration.requirements = [])
    (empty : requests state.core root = []) (support : List (Occurrence roles)) :
    requests (GeneralNominalCenteredSteps.install state.core plan support) root = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  obtain ⟨site,present,alias,within⟩ := mem_requests_iff.mp member
  have sites : (GeneralNominalCenteredSteps.install state.core plan support).erased.current.sites =
      state.core.erased.current.sites := by
    simp [GeneralNominalCenteredSteps.install,GeneralNominalSharedSteps.install,
      GeneralNominalFeedbackSites.install,GeneralNominalSharedEmission.emitted,children_empty plan leaf]
  rw [sites] at present
  have old := GeneralNominalReobservationMergeDiamond.alias_of_same_edges
    (before := (GeneralNominalCenteredSteps.install state.core plan support).erased.current)
    (after := state.core.erased.current) rfl alias
  have bad := mem_requests_iff.mpr ⟨site,present,old,within⟩
  rw [empty] at bad
  cases bad

theorem output_equations_empty (plan : Plan roles)
    (empty : requests state.core root = []) (model : Assignment) :
    OutputEquations state.core root plan model := by
  constructor
  · simp [outputSchema,empty,Plan.schema,GeneralNominalMaterialization.generated,Plan.SchemaHolds]
  · intro first member
    rw [empty] at member
    cases member

theorem initial_installation_model (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (leaf : candidate.packet.declaration.requirements = []) (empty : root.demand.outputs = [])
    (support : List (Occurrence roles)) :
    ∃ model, GeneralNominalCenteredHeadStepKernel.InstallationModels state candidate support model := by
  obtain ⟨model,current,holds⟩ := initial_plan checked source candidate frame leaf empty
  have requestsEmpty : requests state.core candidate.packet.site.occurrence = [] := by
    rw [frame.occurrence_eq]
    obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
    subst state
    rw [GeneralNominalHeadInitialEffects188.initial_requests,empty]
  refine ⟨model,current,holds,output_equations_empty candidate requestsEmpty model,?_,?_⟩
  · exact output_equations_empty (state := ⟨GeneralNominalCenteredSteps.install state.core candidate support,[]⟩)
      candidate (installed_requests_empty candidate leaf requestsEmpty support) model
  · obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
    subst state
    simp [initial]

theorem initial_selected_installable (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (selected : GeneralNominalCenteredHeadWFBoundary.Local registry state root (.selected key children))
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (leaf : candidate.packet.declaration.requirements = []) (empty : root.demand.outputs = []) :
    ∃ support, GeneralNominalCenteredHeadStepKernel.Installable registry state candidate support := by
  have requestsEmpty : requests state.core root = [] := by
    obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
    subst state
    rw [GeneralNominalHeadInitialEffects188.initial_requests,empty]
  have ready := GeneralNominalHeadInitialEffects188.empty_effects_ready requestsEmpty candidate
  have localOld := GeneralNominalCenteredHeadWFBoundary.local_iff.mp selected
  have localPlan : GeneralNominalCenteredHeadStepBoundary.Local registry state candidate.packet.site.occurrence
      (.selected candidate.packet.declaration.id children) := by
    simpa only [frame.occurrence_eq,frame.key_eq] using localOld
  have framePlan : Frame registry state.core candidate.packet.site.occurrence candidate.packet.declaration.id candidate := by
    simpa only [frame.occurrence_eq,frame.key_eq] using frame
  apply (GeneralNominalCenteredHeadStepAvailability.selected_installable_iff localPlan framePlan
    (by simpa only [frame.occurrence_eq] using ready)).mpr
  refine ⟨?_,?_,[],?_,initial_installation_model checked source candidate frame leaf empty []⟩
  · change (GeneralNominalPacketSupport.namedSchema candidate.packet).unknown = false
    rw [named_schema_empty candidate leaf (frame.occurrence_eq ▸ empty)]
  · obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
    subst state
    simp [GeneralNominalCycleSteps.ChoiceCompatible,initial,GeneralNominalCenteredSteps.initial,
      GeneralNominalCenteredSteps.initialAt,GeneralNominalSupport.initial,GeneralNominalSaturationState.initial]
  · apply (GeneralNominalCenteredHeadStepAvailability.frame_value_iff framePlan []).mp
    obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
    subst state
    exact GeneralNominalCenteredHeadStepAvailability.selected_initial_value localOld frame

end Yulang.GeneralNominalHeadLeafPlan189
