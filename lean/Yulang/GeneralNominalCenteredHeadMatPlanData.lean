import Yulang.GeneralNominalCenteredHeadMatStepPacketReordering
import Yulang.GeneralNominalPacketCodes

set_option backward.isDefEq.respectTransparency false

/-! Total packet equations depend on persistent report data and center names.
Cached slot tables and administrative history are absent from this comparison. -/
namespace Yulang.GeneralNominalCenteredHeadMatPlanData
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalReportErasure
open GeneralNominalCenteredHeadMatStepPackets
open GeneralNominalCenteredHeadMatPlans (emittedSchema childSchema)
open GeneralNominalCenteredHeadMatEffects (variables)
variable {roles : Roles.RoleDecls} {first last : Plan roles}

structure Same (first last : Plan roles) : Prop where
  registry : first.packet.registry = last.packet.registry
  declaration : first.packet.declaration = last.packet.declaration
  input : first.input = last.input
  seed : first.packet.context.state.seed = last.packet.context.state.seed
  constructors : first.packet.context.state.constructors = last.packet.context.state.constructors
  interpretation : first.packet.context.interpretation = last.packet.context.interpretation
  report : erase first.packet.context.state (GeneralNominalPacketSupport.report first.packet) =
    erase last.packet.context.state (GeneralNominalPacketSupport.report last.packet)

theorem occurrence (same : Same first last) : first.packet.site.occurrence = last.packet.site.occurrence :=
  first.input_exact.symm.trans ((congrArg Site.occurrence same.input).trans last.input_exact)

theorem bindings (same : Same first last) : first.packet.bindings = last.packet.bindings := by
  have equal := congrArg Data.bindings same.report
  simpa only [bindings_exact,GeneralNominalSaturationState.Packet.bindings,GeneralNominalPacketSupport.report] using equal

theorem capture (same : Same first last) : GeneralNominalPacketSupport.capture first.packet =
    GeneralNominalPacketSupport.capture last.packet := by
  unfold GeneralNominalPacketSupport.capture
  rw [same.registry,occurrence same,same.declaration,bindings same]
  exact GeneralNominalPacketCodes.capture_seed _ _ same.seed _ _ _ _

theorem binder (same : Same first last) (name) : first.binder name = last.binder name := by
  simp only [Plan.binder,capture same,same.declaration,same.seed,occurrence same]

theorem variables_eq (same : Same first last) (model) : variables first model = variables last model := by
  funext mode name
  simp only [variables,same.declaration,binder same,capture same]

theorem ordinary (same : Same first last) (model) :
    GeneralNominalPacketSupport.Ordinary first.packet model ↔ GeneralNominalPacketSupport.Ordinary last.packet model := by
  have checks := congrArg Data.selfChecks same.report
  simp only [checks_exact] at checks
  unfold GeneralNominalPacketSupport.Ordinary
  rw [bindings same,same.registry,occurrence same,same.declaration,checks,
    GeneralNominalPacketCodes.merges_seed _ _ same.seed]

theorem projections (same : Same first last) (model) :
    GeneralNominalRecursiveInspection.ProjectionModels first.packet.context.state
      (GeneralNominalPacketSupport.report first.packet) model ↔
    GeneralNominalRecursiveInspection.ProjectionModels last.packet.context.state
      (GeneralNominalPacketSupport.report last.packet) model := by
  rw [← projections_exact,← projections_exact,same.report]

theorem head_schema (same : Same first last) : first.headSchema = last.headSchema := by
  simp only [Plan.headSchema,GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
    same.declaration,same.constructors,same.interpretation]
  rw [same.input]

theorem schema_holds (same : Same first last) (schema model) :
    first.SchemaHolds schema model ↔ last.SchemaHolds schema model := by
  simp only [Plan.SchemaHolds,binder same,capture same,same.declaration]

theorem needed (same : Same first last) (name) :
    GeneralNominalSharedCaptures.Needed first.packet name ↔ GeneralNominalSharedCaptures.Needed last.packet name := by
  simp only [GeneralNominalSharedCaptures.Needed,same.declaration]

theorem emitted_center (same : Same first last) (clause position pattern) :
    first.emittedCenter clause position pattern = last.emittedCenter clause position pattern := by
  simp only [Plan.emittedCenter,binder same,same.seed,occurrence same,same.declaration]

theorem clause_child (same : Same first last) (clause : Clause) (valid : clause.Signature roles) :
    GeneralNominalFeedbackSites.clauseChild first.packet clause valid =
      GeneralNominalFeedbackSites.clauseChild last.packet clause valid := by
  unfold GeneralNominalFeedbackSites.clauseChild GeneralNominalFeedbackSites.frame
  rw [bindings same,same.registry,occurrence same,same.declaration,
    GeneralNominalPacketCodes.frame_seed _ _ same.seed]

theorem child_site (same : Same first last) (clause : Clause) (valid : clause.Signature roles) :
    first.childSite clause valid = last.childSite clause valid := by
  unfold Plan.childSite
  simp only [emitted_center same]
  congr 1
  exact clause_child same clause valid

theorem child_requests (same : Same first last) (clause : Clause) (valid : clause.Signature roles) :
    first.childRequests clause valid = last.childRequests clause valid := by
  simp only [Plan.childRequests,Plan.childSite,emitted_center same]

theorem emitted_schema (same : Same first last) : emittedSchema first = emittedSchema last := by
  unfold emittedSchema GeneralNominalCenteredHeadMatSchemas.requests
  have alloc := GeneralNominalPacketCodes.allocation_seed (roles := roles) _ _ same.seed
    last.packet.registry last.packet.site.occurrence.identity last.packet.declaration.id
  have cap := capture same
  unfold GeneralNominalPacketSupport.capture at cap
  simp only [same.registry,occurrence same,same.declaration,bindings same] at cap ⊢
  rw [cap,alloc,same.interpretation]

theorem child_schema (same : Same first last) (clause : Clause) (valid : clause.Signature roles) :
    childSchema first clause valid = childSchema last clause valid := by
  simp only [childSchema,same.registry,same.interpretation,child_requests same]

theorem children (same : Same first last) : first.packet.children = last.packet.children := by
  unfold GeneralNominalSaturationState.Packet.children GeneralNominalAllocation.children
  simp only [same.registry,occurrence same,same.declaration,bindings same,
    GeneralNominalPacketCodes.frame_seed _ _ same.seed]

theorem delta (same : Same first last) (model) :
    (Inputs first model ∧ Outputs first model) ↔ (Inputs last model ∧ Outputs last model) := by
  unfold Inputs Outputs
  simp only [ordinary same,projections same,same.input,needed same,binder same,capture same,
    head_schema same,schema_holds same,emitted_schema same,variables_eq same,child_site same,child_schema same,same.declaration]

theorem emitted_mem (same : Same first last) (site : Site roles) : site ∈ first.emitted ↔ site ∈ last.emitted := by
  suffices forward : ∀ {first last : Plan roles}, Same first last → site ∈ first.emitted → site ∈ last.emitted from
    ⟨forward same,forward ⟨same.registry.symm,same.declaration.symm,same.input.symm,same.seed.symm,
      same.constructors.symm,same.interpretation.symm,same.report.symm⟩⟩
  intro first last same member
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp member
  have present : clause.val ∈ last.packet.declaration.requirements := same.declaration ▸ clause.property
  refine List.mem_map.mpr ⟨⟨clause.val,present⟩,List.mem_attach _ _,?_⟩
  exact (child_site same clause.val _).symm

end Yulang.GeneralNominalCenteredHeadMatPlanData
