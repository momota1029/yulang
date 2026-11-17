import Yulang.GeneralNominalVersionedPlans231
set_option backward.isDefEq.respectTransparency false

/-! Conditional semantic comparison with the legacy packet. EndpointAgreement
is an explicit model-level hypothesis, not derived from reachability or assumed
for I44's counterexample repair. No successor boundary claim is made. -/
namespace Yulang.GeneralNominalVersionedConservative231
open GeneralDeclarations GeneralNominalCenters
open GeneralNominalSaturationState (Packet)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedFrame231 (capture binder)
open CommonNominalFullCarrier

 def EndpointAgreement (packet : Packet roles) (model : Assignment) : Prop := ∀ name,
  (model ((capture packet).inputs name).1).1 = (model ((GeneralNominalPacketSupport.capture packet).inputs name).1).1 ∧
  (model ((capture packet).inputs name).2).1 = (model ((GeneralNominalPacketSupport.capture packet).inputs name).2).1

variable {roles : Roles.RoleDecls} {packet : Packet roles} {model : Assignment}

 theorem fits_iff (agreement : EndpointAgreement packet model) (name : Nat) (value : Ty) :
    GeneralNominalCaptureMerges.Fits model ((capture packet).inputs name) value ↔
      GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture packet).inputs name) value := by
  unfold GeneralNominalCaptureMerges.Fits
  rw [(agreement name).1,(agreement name).2]

 theorem variables_eq (plan : Plan roles) (model : Assignment) (agreement : EndpointAgreement plan.packet model) :
    GeneralNominalVersionedPlans231.variables plan model = GeneralNominalCenteredHeadMatEffects.variables plan model := by
  funext mode name
  unfold GeneralNominalVersionedPlans231.variables GeneralNominalCenteredHeadMatEffects.variables
  rw [GeneralNominalVersionedFrame231.binder_eq]
  by_cases output : name ∈ plan.packet.declaration.outputNames
  · simp only [output,ite_true]
  · cases mode <;> simp only [output,ite_false,(agreement name).1,(agreement name).2]

 theorem variableHolds_iff (agreement : EndpointAgreement packet model) (name mode value) :
    GeneralNominalMaterialization.VariableHolds packet.declaration (capture packet) model name mode value ↔
      GeneralNominalMaterialization.VariableHolds packet.declaration (GeneralNominalPacketSupport.capture packet) model name mode value := by
  unfold GeneralNominalMaterialization.VariableHolds
  by_cases output : name ∈ packet.declaration.outputNames
  · simp only [output,ite_true,GeneralNominalVersionedFrame231.capture_outputs]
  · cases mode <;> simp only [output,ite_false,(agreement name).1,(agreement name).2,fits_iff agreement]

 theorem schemaHolds_iff (plan : Plan roles) (model : Assignment) (agreement : EndpointAgreement plan.packet model)
    (schema) : GeneralNominalVersionedPlans231.SchemaHolds plan schema model ↔ plan.SchemaHolds schema model := by
  unfold GeneralNominalVersionedPlans231.SchemaHolds Plan.SchemaHolds
  simp only [GeneralNominalVersionedFrame231.binder_eq,variableHolds_iff agreement]

 private theorem all_flatMap_iff (items : List α) (make : α → List (PresenceNormalForm.Atom Nat)) (model : Assignment) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model (items.flatMap make) ↔
      ∀ item ∈ items, PresenceNormalForm.All CommonNominalFullCarrier.model model (make item) := by
  constructor
  · intro held item member atom present
    exact held atom (List.mem_flatMap.mpr ⟨item,member,present⟩)
  · intro held atom member
    obtain ⟨item,present,within⟩ := List.mem_flatMap.mp member
    exact held item present atom within

 theorem merges_iff (packet : Packet roles) (model : Assignment) (agreement : EndpointAgreement packet model) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalVersionedAllocation231.merges packet.context.state packet.registry packet.site.occurrence.identity packet.declaration packet.bindings) ↔
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges packet.context.state packet.registry packet.site.occurrence.identity packet.declaration packet.bindings) := by
  unfold GeneralNominalVersionedAllocation231.merges GeneralNominalAllocation.merges
  rw [all_flatMap_iff,all_flatMap_iff]
  apply forall_congr'; intro name
  apply forall_congr'; intro _
  have pairs (observed : List GeneralSourceState.Interval) :
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalAllocation.equations ((capture packet).inputs name).1 (GeneralNominalAllocation.lower observed) ++
          GeneralNominalAllocation.equations ((capture packet).inputs name).2 (GeneralNominalAllocation.upper observed)) ↔
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalAllocation.equations ((GeneralNominalPacketSupport.capture packet).inputs name).1 (GeneralNominalAllocation.lower observed) ++
          GeneralNominalAllocation.equations ((GeneralNominalPacketSupport.capture packet).inputs name).2 (GeneralNominalAllocation.upper observed)) := by
    rw [PresenceNormalForm.all_append,PresenceNormalForm.all_append,
      GeneralNominalCaptureMerges.equations_exact,GeneralNominalCaptureMerges.equations_exact,
      GeneralNominalCaptureMerges.equations_exact,GeneralNominalCaptureMerges.equations_exact,
      (agreement name).1,(agreement name).2]
  cases found : GeneralNominalAllocation.occurrences packet.bindings name with
  | nil => exact pairs []
  | cons first rest =>
    cases rest with
    | nil => rfl
    | cons next tail => exact pairs (first :: next :: tail)

 theorem ordinary_iff (packet : Packet roles) (model : Assignment) (agreement : EndpointAgreement packet model) :
    GeneralNominalVersionedPlans231.Ordinary packet model ↔ GeneralNominalPacketSupport.Ordinary packet model := by
  unfold GeneralNominalVersionedPlans231.Ordinary GeneralNominalPacketSupport.Ordinary
  rw [merges_iff packet model agreement]

 theorem child_inputs_values (packet : Packet roles) (model : Assignment) (agreement : EndpointAgreement packet model)
    (clause : Clause) (valid : clause.Signature roles) (index : Fin (roles clause.role).arity) :
    (model (((GeneralNominalVersionedFrame231.clauseChild packet clause valid).demand.arguments index).1)).1 =
      (model (((GeneralNominalFeedbackSites.clauseChild packet clause valid).demand.arguments index).1)).1 ∧
    (model (((GeneralNominalVersionedFrame231.clauseChild packet clause valid).demand.arguments index).2)).1 =
      (model (((GeneralNominalFeedbackSites.clauseChild packet clause valid).demand.arguments index).2)).1 := by
  have general (allocated : GeneralSourceState.Interval) (pattern : GeneralDeclarationPatterns.Pattern) :
      (model ((GeneralDeclarationDemands.inputInterval (capture packet) allocated pattern).1)).1 =
        (model ((GeneralDeclarationDemands.inputInterval (GeneralNominalPacketSupport.capture packet) allocated pattern).1)).1 ∧
      (model ((GeneralDeclarationDemands.inputInterval (capture packet) allocated pattern).2)).1 =
        (model ((GeneralDeclarationDemands.inputInterval (GeneralNominalPacketSupport.capture packet) allocated pattern).2)).1 := by
    unfold GeneralDeclarationDemands.inputInterval
    cases GeneralDeclarationPatterns.normalize pattern <;> first | exact agreement _ | exact ⟨rfl,rfl⟩
  exact general _ _

 theorem childSite_holds_iff (plan : Plan roles) (model : Assignment) (agreement : EndpointAgreement plan.packet model)
    (clause : Clause) (valid : clause.Signature roles) :
    (GeneralNominalVersionedFrame231.childSite plan clause valid).Holds model ↔ (plan.childSite clause valid).Holds model := by
  unfold Site.Holds
  apply forall_congr'; intro index
  unfold GeneralNominalCaptureMerges.Fits
  rw [GeneralNominalVersionedFrame231.childSite_center_eq]
  have lo := (child_inputs_values plan.packet model agreement clause valid index).1
  have hi := (child_inputs_values plan.packet model agreement clause valid index).2
  change (model (((GeneralNominalVersionedFrame231.childSite plan clause valid).occurrence.demand.arguments index).1)).1 =
    (model (((plan.childSite clause valid).occurrence.demand.arguments index).1)).1 at lo
  change (model (((GeneralNominalVersionedFrame231.childSite plan clause valid).occurrence.demand.arguments index).2)).1 =
    (model (((plan.childSite clause valid).occurrence.demand.arguments index).2)).1 at hi
  rw [lo,hi]

/-- Terminal declarations have no child materialization targets to rebase.
Their emitted schema is literally unchanged, independently of the model. -/
 theorem terminal_emittedSchema_eq (plan : Plan roles) (terminal : plan.packet.declaration.requirements = []) :
    GeneralNominalVersionedPlans231.emittedSchema plan = GeneralNominalCenteredHeadMatPlans.emittedSchema plan := by
  have empty (captured : GeneralDeclarationDemands.Capture)
      (allocate : (clause : Clause) → GeneralDeclarationDemands.Allocation roles clause) :
      GeneralCanonicalChildOrder.canonicalEmit plan.packet.site.occurrence.identity
        plan.packet.declaration plan.packet.checked captured allocate = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [GeneralCanonicalChildOrder.canonicalEmit,GeneralDeclarationDemands.emitAll_length]
    simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,terminal]
  unfold GeneralNominalVersionedPlans231.emittedSchema GeneralNominalCenteredHeadMatPlans.emittedSchema
    GeneralNominalVersionedPlans231.emittedRequests GeneralNominalCenteredHeadMatSchemas.requests
  rw [empty,empty]

/-- Exact conditional legacy/new comparison for the terminal fragment only.
The endpoint-value agreement is explicit and is not true automatically in the
cycle230 stale-aggregate model. Nonterminal full packet comparison is open. -/
 theorem terminal_holds_iff (plan : Plan roles) (model : Assignment)
    (agreement : EndpointAgreement plan.packet model) (terminal : plan.packet.declaration.requirements = []) :
    GeneralNominalVersionedPlans231.Holds plan model ↔ GeneralNominalCenteredHeadMatStepPackets.Holds plan model := by
  unfold GeneralNominalVersionedPlans231.Holds GeneralNominalCenteredHeadMatStepPackets.Holds
    GeneralNominalVersionedPlans231.Inputs GeneralNominalCenteredHeadMatStepPackets.Inputs
    GeneralNominalVersionedPlans231.Outputs GeneralNominalCenteredHeadMatStepPackets.Outputs
  simp only [ordinary_iff plan.packet model agreement,GeneralNominalVersionedFrame231.binder_eq,
    fits_iff agreement,schemaHolds_iff plan model agreement,terminal_emittedSchema_eq plan terminal,
    variables_eq plan model agreement,terminal,List.not_mem_nil,false_implies]

end Yulang.GeneralNominalVersionedConservative231
