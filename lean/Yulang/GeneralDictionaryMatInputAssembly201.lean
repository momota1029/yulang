import Yulang.GeneralDictionaryMatInputVariables201

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryMatInputAssembly201
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatSchemas GeneralNominalCenteredHeadMatEffects
open GeneralDictionaryMatInputVariables201
variable {roles : Roles.RoleDecls} (plan : Plan roles)

theorem root_outputs_of_class (state : GeneralNominalCenteredSteps.State roles)
    (recorded : plan.packet.site ∈ state.erased.current.sites)
    (assignment : Assignment)
    (effects : ClassEffects state plan.packet.site.occurrence plan assignment) :
    (generated plan.packet.registry.constructors plan.packet.context.interpretation
      (GeneralNominalMaterialization.rootRequests plan.packet.declaration plan.packet.site.occurrence)).Holds
      (variables plan assignment) assignment := by
  apply GeneralDictionaryMatTerminalAssembly200.generated_holds
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

theorem outputs_of_class (state : GeneralNominalCenteredSteps.State roles)
    (recorded : plan.packet.site ∈ state.erased.current.sites)
    (assignment : Assignment)
    (effects : ClassEffects state plan.packet.site.occurrence plan assignment)
    (restricted : InputVariableClauses plan.packet.declaration) :
    GeneralNominalCenteredHeadMatStepPackets.Outputs plan assignment := by
  apply GeneralDictionaryMatTerminalAssembly200.generated_holds
  intro request member
  rcases List.mem_append.mp member with rootRequest | emitted
  · have root := root_outputs_of_class plan state recorded assignment effects
    exact generated_request_holds _ _ _ _ _ root request rootRequest
  · obtain ⟨emission,present,within⟩ := List.mem_flatMap.mp emitted
    have perm := GeneralCanonicalChildOrder.canonicalEmit_perm plan.packet.site.occurrence.identity
      plan.packet.declaration plan.packet.checked
      (GeneralNominalAllocation.capture plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration.id plan.packet.bindings)
      (GeneralNominalAllocation.allocation plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration.id)
    obtain ⟨clause,_,rfl⟩ := List.mem_map.mp (perm.mem_iff.mpr present)
    exact emission_holds plan assignment clause.val _ (restricted clause.val clause.property).1
      (fun pattern member => by
        obtain ⟨name,equal,_,notOutput⟩ := (restricted clause.val clause.property).2 pattern member
        exact ⟨name,equal,notOutput⟩) request within

/-- Nonterminal total packet assembly without child semantic premises. -/
theorem holds_of_head_class (state : GeneralNominalCenteredSteps.State roles)
    (recorded : plan.packet.site ∈ state.erased.current.sites)
    (assignment : Assignment)
    (headModels : GeneralNominalCenteredHeadCandidates.HeadModels plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds assignment)
    (headEquations : GeneralNominalCenteredHeadOutputs.HeadEquations plan assignment)
    (effects : ClassEffects state plan.packet.site.occurrence plan assignment)
    (restricted : InputVariableClauses plan.packet.declaration) :
    GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment := by
  have privateModels : GeneralNominalState.Models plan.packet.privateContext.state assignment := headModels.1
  have base := (GeneralNominalPacketSupport.private_exact plan.packet assignment).mp privateModels
  have outputs := outputs_of_class plan state recorded assignment effects restricted
  refine ⟨base.1,⟨base.2,headModels.2,headEquations.1,?_,headEquations.2.2,?_,?_⟩,outputs⟩
  · intro name member
    exact headEquations.2.1 name (member.elim id (needed_input plan restricted name))
  · intro equation member _
    exact outputs equation member
  · intro clause member valid
    exact ⟨child_site_holds plan assignment clause valid (fun pattern present => by
        obtain ⟨name,equal,input,_⟩ := (restricted clause member).2 pattern present
        exact ⟨name,equal,input⟩) headEquations,
      child_schema_holds plan assignment clause valid (fun pattern present => by
        obtain ⟨name,equal,_,_⟩ := (restricted clause member).2 pattern present
        exact ⟨name,equal⟩)⟩

end Yulang.GeneralDictionaryMatInputAssembly201
