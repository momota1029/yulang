import Yulang.GeneralNominalCandidateReordering
import Yulang.GeneralNominalCenteredSteps

/-! Concrete packet rebasing at a fixed observation context. Allocation names,
canonical children, branch models, and the input/output schemas are preserved. -/
namespace Yulang.GeneralNominalPacketReordering
open GeneralDeclarations GeneralRegistryReordering GeneralSourceDictionaries
open GeneralNominalSaturationState (Packet)

variable {roles : Roles.RoleDecls} {original : Packet roles} {registry : Registry}
variable {declaration : Declaration}

def rebase (original : Packet roles) (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration) : Packet roles :=
  ⟨registry,original.context,original.site,declaration,
    GeneralNominalCandidateReordering.checked_declaration order pair original.checked,original.bounds⟩

theorem bindings (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration) :
    (rebase original order pair).bindings = original.bindings := by
  unfold Packet.bindings
  dsimp only [rebase]
  rw [GeneralDictionaryRecursiveOrder.report_reorders original.context _ _ pair]

theorem capture (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration) :
    GeneralNominalPacketSupport.capture (rebase original order pair) =
      GeneralNominalPacketSupport.capture original := by
  unfold GeneralNominalPacketSupport.capture
  rw [bindings]
  dsimp only [rebase]
  rw [pair.id]
  rfl

theorem children (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration) :
    (rebase original order pair).children = original.children := by
  unfold Packet.children
  rw [bindings]
  exact (GeneralNominalRegistryOrder.children order pair original.context.state original.site.occurrence
    original.checked (rebase original order pair).checked original.bindings).symm

theorem private_models (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration) (model) :
    GeneralNominalState.Models (rebase original order pair).privateContext.state model ↔
      GeneralNominalState.Models original.privateContext.state model :=
  (GeneralNominalRegistryOrder.private_models pair original.context original.site.occurrence original.bounds model).symm

theorem holds (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration)
    (roleEq : original.registry.roles = roles) (model) :
    (rebase original order pair).Holds model ↔ original.Holds model :=
  (GeneralNominalRegistryOrder.branch_models order roleEq pair original.context original.site.occurrence
    original.checked (rebase original order pair).checked original.bounds model).symm

theorem named_schema (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration)
    (roleEq : original.registry.roles = roles) :
    GeneralNominalPacketSupport.namedSchema (rebase original order pair) =
      GeneralNominalPacketSupport.namedSchema original :=
  (GeneralNominalRegistryOrder.generated order roleEq pair original.context original.site.occurrence
    original.checked (rebase original order pair).checked original.bounds).symm

theorem input_requests (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration) :
    GeneralNominalPacketSupport.inputRequests (rebase original order pair) =
      GeneralNominalPacketSupport.inputRequests original := by
  have allocation : GeneralNominalAllocation.allocation (roles := roles) original.context.state registry
      original.site.occurrence.identity declaration.id =
      GeneralNominalAllocation.allocation original.context.state original.registry
        original.site.occurrence.identity original.declaration.id := by
    rw [pair.id]; rfl
  unfold GeneralNominalPacketSupport.inputRequests
  rw [capture]
  dsimp only [rebase]
  rw [allocation]
  congr 1
  have checked : DeclarationChecked original.registry.constructors roles declaration :=
    (declarationReorders_checked pair).mp original.checked
  exact (GeneralCanonicalChildOrder.canonicalEmit_reorders _ pair original.checked checked _ _).symm

theorem input_schema (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration) :
    GeneralNominalPacketSupport.inputSchema (rebase original order pair) =
      GeneralNominalPacketSupport.inputSchema original := by
  unfold GeneralNominalPacketSupport.inputSchema
  rw [input_requests]
  rfl

theorem ordinary (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration) (model) :
    GeneralNominalPacketSupport.Ordinary (rebase original order pair) model ↔
      GeneralNominalPacketSupport.Ordinary original model := by
  unfold GeneralNominalPacketSupport.Ordinary GeneralNominalPacketSupport.report
  rw [bindings]
  dsimp only [rebase]
  rw [GeneralDictionaryRecursiveOrder.report_reorders original.context _ _ pair]
  simp only [GeneralNominalAllocation.merges,Declaration.inputNames,pair.head,pair.id,
    GeneralNominalAllocation.capture,GeneralNominalAllocation.source]

theorem inputs (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration) (model) :
    GeneralNominalPacketSupport.Inputs (rebase original order pair) model ↔
      GeneralNominalPacketSupport.Inputs original model := by
  unfold GeneralNominalPacketSupport.Inputs GeneralNominalPacketSupport.report
  rw [ordinary,input_schema,capture]
  dsimp only [rebase]
  rw [GeneralDictionaryRecursiveOrder.report_reorders original.context _ _ pair]
  simp only [GeneralNominalMaterialization.Models,GeneralNominalMaterialization.VariableHolds,
    Declaration.outputNames,pair.outputBinders]
  rfl

theorem outputs (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration)
    (roleEq : original.registry.roles = roles) (model) :
    GeneralNominalPacketSupport.Outputs (rebase original order pair) model ↔
      GeneralNominalPacketSupport.Outputs original model := by
  unfold GeneralNominalPacketSupport.Outputs GeneralNominalPacketSupport.report
  rw [named_schema order pair roleEq,capture]
  dsimp only [rebase]
  rw [GeneralDictionaryRecursiveOrder.report_reorders original.context _ _ pair]
  simp only [GeneralNominalMaterialization.Models,GeneralNominalMaterialization.VariableHolds,
    Declaration.outputNames,pair.outputBinders]
  rfl

theorem allocated_membership (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration) (key) :
    key ∈ (rebase original order pair).privateContext.state.allocated ↔
      key ∈ original.privateContext.state.allocated := by
  change key ∈ original.context.state.allocated ++ GeneralNominalAllocation.keys registry _ ↔
    key ∈ original.context.state.allocated ++ GeneralNominalAllocation.keys original.registry _
  simp only [List.mem_append,GeneralNominalRegistryOrder.keys_membership order]
  rfl

theorem reserved_membership (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration) (name) :
    name ∈ (rebase original order pair).privateContext.state.reserved ↔
      name ∈ original.privateContext.state.reserved := by
  change name ∈ (original.context.state.reserved ++ GeneralNominalAllocation.reserved original.context.state registry _) ++ [] ↔
    name ∈ (original.context.state.reserved ++ GeneralNominalAllocation.reserved original.context.state original.registry _) ++ []
  simp only [List.append_nil,List.mem_append,GeneralNominalAllocation.reserved,List.mem_map,
    GeneralNominalRegistryOrder.keys_membership order,GeneralNominalAllocation.source]
  rfl

theorem clause_child (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration)
    (clause : Clause) (valid : clause.Signature roles) :
    GeneralNominalFeedbackSites.clauseChild (rebase original order pair) clause valid =
      GeneralNominalFeedbackSites.clauseChild original clause valid := by
  unfold GeneralNominalFeedbackSites.clauseChild GeneralNominalFeedbackSites.frame
  rw [bindings]
  simp only [rebase,GeneralDictionaryEmissionPlans.occurrence,GeneralDeclarationDemands.emit,
    GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.outputTarget,
    GeneralNominalAllocation.frame,GeneralNominalAllocation.allocation,GeneralNominalAllocation.capture,
    GeneralNominalAllocation.source,Declaration.outputNames,pair.id,pair.outputBinders]
  rfl

theorem usable (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration)
    (roleEq : original.registry.roles = roles) (name origin) :
    GeneralNominalSharedCaptures.Usable (rebase original order pair) name origin ↔
      GeneralNominalSharedCaptures.Usable original name origin := by
  unfold GeneralNominalSharedCaptures.Usable GeneralNominalSharedCaptures.Captured
    GeneralNominalSharedCaptures.InputBound
  rw [capture]
  simp only [holds order pair roleEq]
  simp only [GeneralNominalSharedCaptures.inheritedReport,rebase,
    GeneralNominalInspection.queries,Declaration.normalHead,pair.head]
  rfl

theorem shared_origin (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration)
    (roleEq : original.registry.roles = roles) (child position origin) :
    GeneralNominalSharedEmission.OriginAt (rebase original order pair) child position origin ↔
      GeneralNominalSharedEmission.OriginAt original child position origin := by
  unfold GeneralNominalSharedEmission.OriginAt GeneralNominalSharedEmission.clauseChild
  simp only [usable order pair roleEq,clause_child]
  exact exists_congr (fun clause => and_congr (pair.requirements.mem_iff.symm) Iff.rfl)

theorem fallback_origin (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration) (child position origin) :
    GeneralNominalFeedbackSites.OriginAt (rebase original order pair) child position origin ↔
      GeneralNominalFeedbackSites.OriginAt original child position origin := by
  unfold GeneralNominalFeedbackSites.OriginAt
  simp only [clause_child]
  dsimp only [rebase]
  rw [GeneralDictionaryRecursiveOrder.report_reorders original.context _ _ pair]
  simp only [Declaration.inputNames,pair.head]
  exact exists_congr (fun clause => and_congr (pair.requirements.mem_iff.symm) Iff.rfl)

open Classical in
private theorem choice_option {α : Type u} {first last : α → Prop}
    (same : ∀ value, first value ↔ last value) (fallback : Option α) :
    (if h : ∃ value, first value then some (Classical.choose h) else fallback) =
      (if h : ∃ value, last value then some (Classical.choose h) else fallback) := by
  have equal : first = last := funext (fun value => propext (same value))
  cases equal
  rfl

theorem fallback_child_origin (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration)
    (child : Occurrence roles) (index : Fin (roles child.demand.role).arity) :
    GeneralNominalFeedbackSites.childOrigin (rebase original order pair) child index =
      GeneralNominalFeedbackSites.childOrigin original child index := by
  classical
  unfold GeneralNominalFeedbackSites.childOrigin
  exact choice_option (fallback_origin order pair child index.val) _

theorem shared_child_origin (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration)
    (roleEq : original.registry.roles = roles)
    (child : Occurrence roles) (index : Fin (roles child.demand.role).arity) :
    GeneralNominalSharedEmission.childOrigin (rebase original order pair) child index =
      GeneralNominalSharedEmission.childOrigin original child index := by
  classical
  unfold GeneralNominalSharedEmission.childOrigin
  rw [fallback_child_origin]
  exact choice_option (shared_origin order pair roleEq child index.val) _

theorem shared_child_site (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration)
    (roleEq : original.registry.roles = roles) (child : Occurrence roles) :
    GeneralNominalSharedEmission.childSite (rebase original order pair) child =
      GeneralNominalSharedEmission.childSite original child := by
  unfold GeneralNominalSharedEmission.childSite
  congr 1
  exact congrArg List.ofFn (funext (shared_child_origin order pair roleEq child))

theorem shared_emitted_sites (order : Reorders original.registry registry)
    (pair : DeclarationReorders original.declaration declaration)
    (roleEq : original.registry.roles = roles) :
    (GeneralNominalSharedEmission.emitted (rebase original order pair)).sites =
      (GeneralNominalSharedEmission.emitted original).sites := by
  change (rebase original order pair).children.map _ = original.children.map _
  rw [children]
  exact List.map_congr_left (fun child _ => shared_child_site order pair roleEq child)

end Yulang.GeneralNominalPacketReordering
