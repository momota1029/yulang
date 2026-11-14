import Yulang.GeneralNominalCenteredHeadMatStepPacketReordering
import Yulang.GeneralNominalCenteredHeadStepInstallationPermutation

set_option backward.isDefEq.respectTransparency false

/-! Corrected plan semantics survive both registry rebasing and replacement
of allocation metadata. Historical contexts remain part of the pairing. -/
namespace Yulang.GeneralNominalCenteredHeadMatPermutationPlans
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering GeneralNominalCenters
open GeneralNominalCenteredPermutationPlans (metadata)
open GeneralNominalCenteredHeadMatStepPackets
open GeneralNominalCenteredHeadMatEffects
open GeneralNominalCenteredHeadMatPlans (emittedSchema childSchema)
variable {roles : Roles.RoleDecls}
variable (plan : Plan roles) (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)

theorem variables_metadata (model) : variables (metadata plan allocated reserved) model = variables plan model := by
  funext mode name
  have cap : GeneralNominalPacketSupport.capture (metadata plan allocated reserved).packet =
      GeneralNominalPacketSupport.capture plan.packet := GeneralNominalPacketMetadata.capture ..
  simp only [variables,GeneralNominalCenteredPermutationPlans.binder,cap]
  rfl

theorem requests_metadata :
    GeneralNominalCenteredHeadMatSchemas.requests (metadata plan allocated reserved).packet.context.state
      (metadata plan allocated reserved).packet.registry (metadata plan allocated reserved).packet.site.occurrence
      (metadata plan allocated reserved).packet.declaration (metadata plan allocated reserved).packet.checked
      (metadata plan allocated reserved).packet.bindings =
    GeneralNominalCenteredHeadMatSchemas.requests plan.packet.context.state plan.packet.registry
      plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bindings := by
  unfold GeneralNominalCenteredHeadMatSchemas.requests
  have cap : GeneralNominalPacketSupport.capture (metadata plan allocated reserved).packet =
      GeneralNominalPacketSupport.capture plan.packet := GeneralNominalPacketMetadata.capture ..
  change _ ++ (GeneralCanonicalChildOrder.canonicalEmit _ _ _
    (GeneralNominalPacketSupport.capture (metadata plan allocated reserved).packet) _).flatMap _ = _
  rw [cap]
  rfl

theorem emitted_metadata : emittedSchema (metadata plan allocated reserved) = emittedSchema plan := by
  unfold emittedSchema
  rw [requests_metadata]
  rfl

theorem child_metadata (clause : Clause) (valid : clause.Signature roles) :
    childSchema (metadata plan allocated reserved) clause valid = childSchema plan clause valid := by
  unfold childSchema
  rw [GeneralNominalCenteredPermutationPlans.child_requests]
  rfl

theorem outputs_metadata (model) : Outputs (metadata plan allocated reserved) model ↔ Outputs plan model := by
  simp only [Outputs,emitted_metadata,variables_metadata]

theorem inputs_metadata (model) : Inputs (metadata plan allocated reserved) model ↔ Inputs plan model := by
  have ordinary : GeneralNominalPacketSupport.Ordinary (metadata plan allocated reserved).packet model ↔
      GeneralNominalPacketSupport.Ordinary plan.packet model := GeneralNominalPacketMetadata.ordinary ..
  have cap : GeneralNominalPacketSupport.capture (metadata plan allocated reserved).packet =
      GeneralNominalPacketSupport.capture plan.packet := GeneralNominalPacketMetadata.capture ..
  have projections := GeneralNominalReportMetadata.projectionModels plan.packet.context.state allocated reserved
    (GeneralNominalPacketSupport.report plan.packet) model
  unfold Inputs
  simp only [ordinary,GeneralNominalCenteredPermutationPlans.binder,
    GeneralNominalCenteredPermutationPlans.head_schema,GeneralNominalCenteredPermutationPlans.schema_holds,
    GeneralNominalCenteredPermutationPlans.child_site,cap,
    emitted_metadata,variables_metadata,child_metadata]
  change (_ ∧ GeneralNominalRecursiveInspection.ProjectionModels _
    (GeneralNominalPacketSupport.report (GeneralNominalPacketMetadata.rebase plan.packet allocated reserved)) _ ∧ _) ↔ _
  rw [GeneralNominalPacketMetadata.report]
  exact and_congr Iff.rfl (and_congr projections Iff.rfl)

theorem head_metadata (model) :
    GeneralNominalCenteredHeadOutputs.HeadEquations (metadata plan allocated reserved) model ↔
      GeneralNominalCenteredHeadOutputs.HeadEquations plan model :=
  GeneralNominalCenteredHeadStepEffectPermutation.metadata_head ..

theorem body_metadata (target body model) :
    BodyHolds (metadata plan allocated reserved) target model body ↔ BodyHolds plan target model body := by
  cases body <;> simp only [BodyHolds,bodySchema,compileBody,bodyVariables,variables_metadata]
  all_goals rfl

theorem ready_metadata (state root) : Ready state root (metadata plan allocated reserved) ↔ Ready state root plan := Iff.rfl

theorem effects_metadata (state root model) :
    ClassEffects state root (metadata plan allocated reserved) model ↔ ClassEffects state root plan model := by
  simp only [ClassEffects,body_metadata]
  rfl

structure Pair (first last : Plan roles) : Prop where
  matched : GeneralNominalCenteredPermutationCounterparts.Match first last
  contexts : GeneralNominalJournalPermutation.ContextPair first.packet.context last.packet.context
  privateContexts : GeneralNominalJournalPermutation.ContextPair first.packet.privateContext last.packet.privateContext
  inputs : ∀ model, Inputs first model ↔ Inputs last model
  outputs : ∀ model, Outputs first model ↔ Outputs last model
  emitted : ∀ site, site ∈ first.emitted ↔ site ∈ last.emitted
  schema : emittedSchema first = emittedSchema last
  head : ∀ model, GeneralNominalCenteredHeadOutputs.HeadEquations first model ↔
    GeneralNominalCenteredHeadOutputs.HeadEquations last model
  ready : ∀ state root, Ready state root first ↔ Ready state root last
  effects : ∀ state root model, ClassEffects state root first model ↔ ClassEffects state root last model

variable {plan allocated reserved}

theorem rebased (order : Reorders plan.packet.registry registry) (roleEq : plan.packet.registry.roles = roles)
    (pair : DeclarationReorders plan.packet.declaration declaration) (allocated reserved)
    (keys : ∀ key, key ∈ allocated ↔ key ∈ plan.packet.context.state.allocated)
    (names : ∀ name, name ∈ reserved ↔ name ∈ plan.packet.context.state.reserved) :
    Pair plan (GeneralNominalCenteredPermutationCounterparts.rebase plan order pair allocated reserved) := by
  have marked := GeneralNominalCenteredPermutationCounterparts.rebased plan order pair allocated reserved keys names
  refine ⟨GeneralNominalCenteredPermutationCounterparts.matched plan order roleEq pair allocated reserved keys names,
    ⟨⟨allocated,reserved,rfl,keys,names⟩,rfl⟩,
    GeneralNominalCenteredPermutationEmission.rebased_private plan.packet marked,?_,?_,?_,?_,?_,?_,?_⟩
  · intro model
    exact (GeneralNominalCenteredHeadMatStepPacketReordering.inputs order pair model).symm.trans
      (inputs_metadata _ allocated reserved model).symm
  · intro model
    exact (GeneralNominalCenteredHeadMatStepPacketReordering.outputs order pair model).symm.trans
      (outputs_metadata _ allocated reserved model).symm
  · exact GeneralNominalCenteredHeadStepTableExtension.rebased_emitted marked rfl
  · change _ = emittedSchema (metadata _ allocated reserved)
    rw [emitted_metadata,GeneralNominalCenteredHeadMatStepPacketReordering.emitted_schema]
  · intro model
    exact (GeneralNominalCenteredHeadStepOrder.head_equations order pair model).symm.trans
      (head_metadata _ allocated reserved model).symm
  · intro state root
    exact (GeneralNominalCenteredHeadMatStepOrder.ready order pair state root).symm.trans
      (ready_metadata _ allocated reserved state root).symm
  · intro state root model
    exact (GeneralNominalCenteredHeadMatStepOrder.class_effects order pair state root model).symm.trans
      (effects_metadata _ allocated reserved state root model).symm

theorem of_rebased (marked : GeneralNominalCenteredPermutationRepresentation.RebasedPacket first last plan.packet other.packet)
    (input : plan.input = other.input) (roleEq : first.roles = roles) : Pair plan other := by
  obtain ⟨registry,declaration,order,pair,allocated,reserved,keys,names,packetEq⟩ := marked
  have equal : other = GeneralNominalCenteredPermutationCounterparts.rebase plan order pair allocated reserved := by
    cases other with
    | mk packet center exactInput =>
      dsimp at packetEq input
      cases packetEq; cases input; rfl
  rw [equal]
  exact rebased order (registry ▸ roleEq) pair allocated reserved keys names

theorem Pair.holds (pair : Pair first last) (model) : Holds first model ↔ Holds last model :=
  and_congr (GeneralNominalMetadataEquivalence.models pair.contexts.state model)
    (and_congr (pair.inputs model) (pair.outputs model))

theorem Pair.symm (pair : Pair first last) : Pair last first :=
  ⟨pair.matched.symm,pair.contexts.symm,pair.privateContexts.symm,
    fun model => (pair.inputs model).symm,fun model => (pair.outputs model).symm,
    fun site => (pair.emitted site).symm,pair.schema.symm,
    fun model => (pair.head model).symm,fun state root => (pair.ready state root).symm,
    fun state root model => (pair.effects state root model).symm⟩

end Yulang.GeneralNominalCenteredHeadMatPermutationPlans
