import Yulang.GeneralDictionaryMatStableScalar200

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryMatTerminalAssembly200
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatSchemas
open GeneralNominalCenteredHeadMatEffects

/-- Schema validity can be assembled request by request. -/
theorem generated_holds (catalogue interpretation requests variables model)
    (valid : ∀ request ∈ requests, (materialize catalogue interpretation request).Holds variables model) :
    (GeneralNominalCenteredHeadMatSchemas.generated catalogue interpretation requests).Holds variables model := by
  induction requests with
  | nil => intro equation member; cases member
  | cons first rest ih =>
    exact append_holds.mpr ⟨valid first (List.mem_cons_self),
      ih (fun request member => valid request (List.mem_cons_of_mem _ member))⟩

variable {roles : Roles.RoleDecls} (plan : Plan roles)

theorem terminal_requests (terminal : plan.packet.declaration.requirements = []) :
    GeneralNominalCenteredHeadMatSchemas.requests plan.packet.context.state plan.packet.registry
      plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bindings =
    GeneralNominalMaterialization.rootRequests plan.packet.declaration plan.packet.site.occurrence := by
  have empty (capture : GeneralDeclarationDemands.Capture)
      (allocate : (clause : Clause) → GeneralDeclarationDemands.Allocation roles clause) :
      GeneralCanonicalChildOrder.canonicalEmit plan.packet.site.occurrence.identity plan.packet.declaration
        plan.packet.checked capture allocate = [] := by
    apply List.eq_nil_of_length_eq_zero
    have length := (GeneralCanonicalChildOrder.canonicalEmit_perm plan.packet.site.occurrence.identity
      plan.packet.declaration plan.packet.checked capture allocate).length_eq.symm
    simpa [GeneralDeclarationDemands.emitAll,terminal] using length
  unfold GeneralNominalCenteredHeadMatSchemas.requests
  rw [empty]
  simp

/-- Registered raw-site requests are a subset of the actual alias-class requests.
No output-equation premise is added: it is extracted from ClassEffects. -/
theorem outputs_of_class (state : GeneralNominalCenteredSteps.State roles)
    (recorded : plan.packet.site ∈ state.erased.current.sites)
    (assignment : Assignment)
    (effects : ClassEffects state plan.packet.site.occurrence plan assignment)
    (terminal : plan.packet.declaration.requirements = []) :
    GeneralNominalCenteredHeadMatStepPackets.Outputs plan assignment := by
  unfold GeneralNominalCenteredHeadMatStepPackets.Outputs GeneralNominalCenteredHeadMatPlans.emittedSchema
  rw [terminal_requests plan terminal]
  apply generated_holds
  intro request member
  obtain ⟨output,requested,within⟩ := List.mem_flatMap.mp member
  obtain ⟨equation,found,rfl⟩ := List.mem_map.mp within
  have found := Option.mem_toList.mp found
  have present : output ∈ GeneralNominalCenteredHeadOutputs.requests state plan.packet.site.occurrence :=
    GeneralNominalCenteredHeadOutputs.request_retained plan.packet.site recorded (.refl _) requested
  have lookup : GeneralDictionaryAssociatedProvenance.lookup roles plan.packet.declaration output.name =
      some (.explicit equation) := by
    simp [GeneralDictionaryAssociatedProvenance.lookup,found]
  exact effects.1 output present (.explicit equation) lookup

/-- Actual total Holds follows from smaller same-model head and class components.
This theorem does not identify separate existential candidate models. -/
theorem holds_of_head_class (state : GeneralNominalCenteredSteps.State roles)
    (recorded : plan.packet.site ∈ state.erased.current.sites)
    (assignment : Assignment)
    (headModels : GeneralNominalCenteredHeadCandidates.HeadModels plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds assignment)
    (headEquations : GeneralNominalCenteredHeadOutputs.HeadEquations plan assignment)
    (effects : ClassEffects state plan.packet.site.occurrence plan assignment)
    (terminal : plan.packet.declaration.requirements = []) :
    GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment := by
  have privateModels : GeneralNominalState.Models plan.packet.privateContext.state assignment := headModels.1
  have base := (GeneralNominalPacketSupport.private_exact plan.packet assignment).mp privateModels
  have outputs := outputs_of_class plan state recorded assignment effects terminal
  refine ⟨base.1,⟨base.2,headModels.2,headEquations.1,?_,headEquations.2.2,?_,?_⟩,outputs⟩
  · intro name member
    rcases member with input | ⟨clause,present,_⟩
    · exact headEquations.2.1 name input
    · rw [terminal] at present
      cases present
  · intro equation member _
    exact outputs equation member
  · intro clause member
    rw [terminal] at member
    cases member

/-- Terminal selected evidence needs only a common head/class model, not an
assumed total packet model. Choice compatibility remains an operational premise. -/
theorem evidence_of_terminal_common_head (effect : GeneralNominalCenteredHeadMatStepJournal.Effect roles)
    (state : GeneralNominalCenteredHeadMatStepJournal.State roles) (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry root state)
    (stable : GeneralNominalCenteredHeadMatStepKernel.Stable registry state effect.plan.packet.site.occurrence)
    (selected : GeneralNominalCenteredHeadMatStepBoundary.Local registry state effect.plan.packet.site.occurrence
      (.selected effect.plan.packet.declaration.id children))
    (registryEq : effect.registry = registry) (snapshot : effect.snapshot = state.core)
    (choice : GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet)
    (common : ∃ model, GeneralNominalCenteredHeadMatStepJournal.Models state model ∧
      GeneralNominalCenteredHeadCandidates.HeadModels effect.plan.packet.registry effect.plan.packet.context
        effect.plan.packet.site.occurrence effect.plan.packet.declaration effect.plan.packet.bounds model ∧
      effect.Holds model)
    (terminal : effect.plan.packet.declaration.requirements = [])
    (defined : GeneralNominalMaterialization.RootDefined effect.plan.packet.declaration effect.plan.packet.site.occurrence)
    (scalars : GeneralDictionaryMatScalarOutputs200.ScalarRequests effect.plan.packet.registry effect.plan.packet.context
      (GeneralNominalMaterialization.rootRequests effect.plan.packet.declaration effect.plan.packet.site.occurrence))
    (assignment : Assignment) (models : GeneralNominalCenteredHeadMatStepJournal.Models state assignment) :
    (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence registry state assignment
      effect.plan.packet.site.occurrence (.node effect.plan.packet.declaration.id []) := by
  have full : ∃ model, GeneralNominalCenteredHeadMatStepJournal.Models state model ∧
      GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧ effect.Holds model := by
    obtain ⟨model,valid,head,chosen⟩ := common
    exact ⟨model,valid,holds_of_head_class effect.plan effect.snapshot effect.frame.raw_recorded
      model head chosen.1 chosen.2 terminal,chosen⟩
  refine GeneralDictionaryMatStableScalar200.evidence_of_common_model effect checked reachable stable selected
    registryEq snapshot choice full ?_ defined scalars assignment models [] ?_
  · intro clause member
    rw [terminal] at member
    cases member
  · have empty : effect.plan.packet.children = [] :=
      GeneralDictionaryLinearLeaf.children_empty effect.plan.packet.context effect.plan.packet.registry
        effect.plan.packet.site.occurrence effect.plan.packet.declaration effect.plan.packet.checked terminal _
    rw [empty]
    exact .nil

end Yulang.GeneralDictionaryMatTerminalAssembly200
