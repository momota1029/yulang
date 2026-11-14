import Yulang.GeneralNominalCenteredHeadMatStepOrder

set_option backward.isDefEq.respectTransparency false

/-! Registry rebasing preserves the complete materialization equations at a
fixed observation context, including variable endpoint requests. Class defaults
are transported by the companion StepOrder class-effect theorem. -/
namespace Yulang.GeneralNominalCenteredHeadMatStepPacketReordering
open GeneralDeclarations GeneralRegistryReordering GeneralNominalCenters
open GeneralNominalCenteredPlanReordering (rebase)
open GeneralNominalCenteredHeadMatPlans (emittedSchema childSchema)
open GeneralNominalCenteredHeadMatEffects (variables)
open GeneralNominalCenteredHeadMatStepPackets
variable {roles : Roles.RoleDecls} {plan : Plan roles} {registry : Registry} {declaration : Declaration}

theorem variables_rebase (order : Reorders plan.packet.registry registry)
    (pair : DeclarationReorders plan.packet.declaration declaration) (model) :
    variables (rebase plan order pair) model = variables plan model := by
  funext mode name
  have capture : GeneralNominalPacketSupport.capture (rebase plan order pair).packet =
      GeneralNominalPacketSupport.capture plan.packet := GeneralNominalPacketReordering.capture order pair
  simp only [variables,GeneralNominalCenteredPlanReordering.binder,capture]
  change (if name ∈ declaration.outputNames then _ else _) = _
  simp only [Declaration.outputNames,pair.outputBinders]

theorem requests_rebase (order : Reorders plan.packet.registry registry)
    (pair : DeclarationReorders plan.packet.declaration declaration) :
    GeneralNominalCenteredHeadMatSchemas.requests (rebase plan order pair).packet.context.state
      (rebase plan order pair).packet.registry (rebase plan order pair).packet.site.occurrence
      (rebase plan order pair).packet.declaration (rebase plan order pair).packet.checked (rebase plan order pair).packet.bindings =
    GeneralNominalCenteredHeadMatSchemas.requests plan.packet.context.state plan.packet.registry
      plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bindings := by
  have cap := GeneralNominalPacketReordering.capture (original := plan.packet) order pair
  have allocation : GeneralNominalAllocation.allocation (roles := roles) plan.packet.context.state registry
      plan.packet.site.occurrence.identity declaration.id =
      GeneralNominalAllocation.allocation plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration.id := by
    rw [pair.id]; rfl
  unfold GeneralNominalCenteredHeadMatSchemas.requests
  change GeneralNominalMaterialization.rootRequests declaration plan.packet.site.occurrence ++ _ = _
  have root : GeneralNominalMaterialization.rootRequests declaration plan.packet.site.occurrence =
      GeneralNominalMaterialization.rootRequests plan.packet.declaration plan.packet.site.occurrence := by
    simp only [GeneralNominalMaterialization.rootRequests,pair.associated]
  rw [root]
  congr 1
  change (GeneralCanonicalChildOrder.canonicalEmit _ declaration _
      (GeneralNominalPacketSupport.capture (GeneralNominalPacketReordering.rebase plan.packet order pair)) _).flatMap _ = _
  rw [cap]
  dsimp only [rebase,GeneralNominalPacketReordering.rebase]
  rw [allocation]
  congr 1
  have checked : DeclarationChecked plan.packet.registry.constructors roles declaration :=
    (declarationReorders_checked pair).mp plan.packet.checked
  exact (GeneralCanonicalChildOrder.canonicalEmit_reorders _ pair plan.packet.checked checked _ _).symm

theorem emitted_schema (order : Reorders plan.packet.registry registry)
    (pair : DeclarationReorders plan.packet.declaration declaration) :
    emittedSchema (rebase plan order pair) = emittedSchema plan := by
  unfold emittedSchema
  rw [requests_rebase]
  change GeneralNominalCenteredHeadMatSchemas.generated registry.constructors _ _ = _
  rw [order.1]
  rfl

theorem child_schema (order : Reorders plan.packet.registry registry)
    (pair : DeclarationReorders plan.packet.declaration declaration) (clause : Clause) (valid : clause.Signature roles) :
    childSchema (rebase plan order pair) clause valid = childSchema plan clause valid := by
  unfold childSchema
  rw [GeneralNominalCenteredPlanReordering.child_requests]
  change GeneralNominalCenteredHeadMatSchemas.generated registry.constructors _ _ = _
  rw [order.1]
  rfl

theorem outputs (order : Reorders plan.packet.registry registry)
    (pair : DeclarationReorders plan.packet.declaration declaration) (model) :
    Outputs (rebase plan order pair) model ↔ Outputs plan model := by
  simp only [Outputs,emitted_schema,variables_rebase]

theorem inputs (order : Reorders plan.packet.registry registry)
    (pair : DeclarationReorders plan.packet.declaration declaration) (model) :
    Inputs (rebase plan order pair) model ↔ Inputs plan model := by
  have cap : GeneralNominalPacketSupport.capture (rebase plan order pair).packet =
      GeneralNominalPacketSupport.capture plan.packet := GeneralNominalPacketReordering.capture order pair
  have ordinary : GeneralNominalPacketSupport.Ordinary (rebase plan order pair).packet model ↔
      GeneralNominalPacketSupport.Ordinary plan.packet model := GeneralNominalPacketReordering.ordinary order pair model
  unfold Inputs
  simp only [ordinary,GeneralNominalCenteredPlanReordering.binder,
    GeneralNominalCenteredPlanReordering.needed,GeneralNominalCenteredPlanReordering.head_schema,
    GeneralNominalCenteredPlanReordering.schema_holds,GeneralNominalCenteredPlanReordering.child_site,
    cap,emitted_schema,variables_rebase,child_schema]
  simp only [GeneralNominalPacketSupport.report,rebase,GeneralNominalPacketReordering.rebase,
    GeneralDictionaryRecursiveOrder.report_reorders _ _ _ pair,Declaration.inputNames,pair.head]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  exact forall_congr' (fun clause => imp_congr pair.requirements.mem_iff.symm Iff.rfl)

theorem holds (order : Reorders plan.packet.registry registry)
    (pair : DeclarationReorders plan.packet.declaration declaration) (model) :
    Holds (rebase plan order pair) model ↔ Holds plan model :=
  and_congr Iff.rfl (and_congr (inputs order pair model) (outputs order pair model))

end Yulang.GeneralNominalCenteredHeadMatStepPacketReordering
