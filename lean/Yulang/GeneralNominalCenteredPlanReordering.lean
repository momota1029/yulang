import Yulang.GeneralNominalPacketReordering

set_option backward.isDefEq.respectTransparency false

/-! Rebased centered plans keep their input centers and all model equations.
Where enumeration changes only the order of their emitted centered sites. -/
namespace Yulang.GeneralNominalCenteredPlanReordering
open GeneralDeclarations GeneralRegistryReordering GeneralSourceDictionaries
open GeneralNominalCenters

variable {roles : Roles.RoleDecls} {original : Plan roles} {registry : Registry}
variable {declaration : Declaration}

def rebase (original : Plan roles) (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration) : Plan roles :=
  ⟨GeneralNominalPacketReordering.rebase original.packet order pair,original.input,original.input_exact⟩

theorem binder (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration) (name) :
    (rebase original order pair).binder name = original.binder name := by
  unfold Plan.binder
  simp only [rebase,GeneralNominalPacketReordering.capture]
  dsimp only [GeneralNominalPacketReordering.rebase]
  simp only [Declaration.outputNames,pair.outputBinders,pair.id]

theorem head_schema (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration) :
    (rebase original order pair).headSchema = original.headSchema := by
  simp only [Plan.headSchema,rebase,GeneralNominalPacketReordering.rebase,
    GeneralNominalInspection.queries,Declaration.normalHead,pair.head]

theorem schema_holds (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration) (schema model) :
    (rebase original order pair).SchemaHolds schema model ↔ original.SchemaHolds schema model := by
  unfold Plan.SchemaHolds
  simp only [binder]
  dsimp only [rebase]
  rw [GeneralNominalPacketReordering.capture]
  simp only [GeneralNominalPacketReordering.rebase,GeneralNominalMaterialization.VariableHolds,
    Declaration.outputNames,pair.outputBinders]

theorem emitted_center (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration) (clause position pattern) :
    (rebase original order pair).emittedCenter clause position pattern =
      original.emittedCenter clause position pattern := by
  unfold Plan.emittedCenter
  split
  · exact binder order pair _
  · simp only [rebase,GeneralNominalPacketReordering.rebase,pair.id]

theorem child_site (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration)
    (clause : Clause) (valid : clause.Signature roles) :
    (rebase original order pair).childSite clause valid = original.childSite clause valid := by
  unfold Plan.childSite
  congr 1
  · exact GeneralNominalPacketReordering.clause_child order pair clause valid
  · funext index
    exact emitted_center order pair _ _ _

theorem child_requests (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration)
    (clause : Clause) (valid : clause.Signature roles) :
    (rebase original order pair).childRequests clause valid = original.childRequests clause valid := by
  simp only [Plan.childRequests,Plan.childSite,emitted_center]

theorem needed (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration) (name) :
    GeneralNominalSharedCaptures.Needed (rebase original order pair).packet name ↔
      GeneralNominalSharedCaptures.Needed original.packet name := by
  unfold GeneralNominalSharedCaptures.Needed
  exact exists_congr (fun clause => and_congr pair.requirements.mem_iff.symm Iff.rfl)

theorem equations (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration)
    (roleEq : original.packet.registry.roles = roles) (model) :
    (rebase original order pair).Equations model ↔ original.Equations model := by
  have cap : GeneralNominalPacketSupport.capture (rebase original order pair).packet =
      GeneralNominalPacketSupport.capture original.packet := GeneralNominalPacketReordering.capture order pair
  have inp : GeneralNominalPacketSupport.inputSchema (rebase original order pair).packet =
      GeneralNominalPacketSupport.inputSchema original.packet := GeneralNominalPacketReordering.input_schema order pair
  have out : GeneralNominalPacketSupport.namedSchema (rebase original order pair).packet =
      GeneralNominalPacketSupport.namedSchema original.packet := GeneralNominalPacketReordering.named_schema order pair roleEq
  unfold Plan.Equations
  simp only [needed,binder,head_schema,cap,inp,out,schema_holds,child_requests,child_site]
  change (original.input.Holds model ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ↔ _
  simp only [Plan.schema,rebase,GeneralNominalPacketReordering.rebase,
    Declaration.inputNames,pair.head]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  exact forall_congr' (fun clause => imp_congr pair.requirements.mem_iff.symm Iff.rfl)

theorem holds (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration)
    (roleEq : original.packet.registry.roles = roles) (model) :
    (rebase original order pair).Holds model ↔ original.Holds model :=
  and_congr (GeneralNominalPacketReordering.holds order pair roleEq model)
    (equations order pair roleEq model)

theorem emitted_mem (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration) (site : Site roles) :
    site ∈ (rebase original order pair).emitted ↔ site ∈ original.emitted := by
  unfold Plan.emitted
  simp only [List.mem_map,List.mem_attach,true_and,Subtype.exists]
  constructor
  · rintro ⟨clause,member,same⟩
    refine ⟨clause,pair.requirements.mem_iff.mpr member,?_⟩
    rw [child_site] at same
    exact same
  · rintro ⟨clause,member,same⟩
    refine ⟨clause,pair.requirements.mem_iff.mp member,?_⟩
    rw [child_site]
    exact same

theorem emitted_perm (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration) :
    (rebase original order pair).emitted.Perm original.emitted := by
  unfold Plan.emitted
  simp only [child_site]
  have moved := List.Perm.pmap (fun clause valid => original.childSite clause valid)
    pair.requirements.symm
    (H₁ := (rebase original order pair).packet.checked.signature.2.2.2)
    (H₂ := original.packet.checked.signature.2.2.2)
  simpa only [List.pmap_eq_map_attach,rebase,GeneralNominalPacketReordering.rebase] using moved

theorem child_schema (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration)
    (clause : Clause) (valid : clause.Signature roles) :
    (rebase original order pair).schema ((rebase original order pair).childRequests clause valid) =
      original.schema (original.childRequests clause valid) := by
  rw [child_requests]
  rfl

theorem tests_mem (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration)
    (roleEq : original.packet.registry.roles = roles) (entry) :
    entry ∈ GeneralNominalCenteredSteps.Plan.tests (rebase original order pair) ↔
      entry ∈ GeneralNominalCenteredSteps.Plan.tests original := by
  have named : GeneralNominalPacketSupport.namedSchema (rebase original order pair).packet =
      GeneralNominalPacketSupport.namedSchema original.packet :=
    GeneralNominalPacketReordering.named_schema order pair roleEq
  unfold GeneralNominalCenteredSteps.Plan.tests
  simp only [head_schema,named,child_schema,List.mem_append,List.mem_flatMap,List.mem_attach,
    true_and,Subtype.exists]
  apply or_congr Iff.rfl
  apply exists_congr
  intro clause
  constructor
  · rintro ⟨member,test⟩
    exact ⟨pair.requirements.mem_iff.mpr member,test⟩
  · rintro ⟨member,test⟩
    exact ⟨pair.requirements.mem_iff.mp member,test⟩

theorem inspection (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration) :
    GeneralNominalCenteredSteps.inspection (rebase original order pair) =
      GeneralNominalCenteredSteps.inspection original := by
  simp only [GeneralNominalCenteredSteps.inspection,rebase,GeneralNominalPacketReordering.rebase,
    GeneralNominalInspection.queries,Declaration.normalHead,pair.head]

theorem safe (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration)
    (state : GeneralNominalCenteredSteps.State roles) :
    GeneralNominalCenteredSteps.Safe state (rebase original order pair) ↔
      GeneralNominalCenteredSteps.Safe state original := by
  unfold GeneralNominalCenteredSteps.Safe
  rw [inspection]

theorem installed_models (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration)
    (roleEq : original.packet.registry.roles = roles)
    (state : GeneralNominalCenteredSteps.State roles)
    (same : original.packet.context = state.erased.current.context) (support model) :
    GeneralNominalCenteredSteps.Models
        (GeneralNominalCenteredSteps.install state (rebase original order pair) support) model ↔
      GeneralNominalCenteredSteps.Models
        (GeneralNominalCenteredSteps.install state original support) model := by
  rw [GeneralNominalCenteredSteps.install_models (plan := rebase original order pair) same,
    GeneralNominalCenteredSteps.install_models same]
  exact and_congr Iff.rfl (holds order pair roleEq model)

theorem installed_raw_sites (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration)
    (roleEq : original.packet.registry.roles = roles)
    (state : GeneralNominalCenteredSteps.State roles) (support) :
    (GeneralNominalCenteredSteps.install state (rebase original order pair) support).erased.current.sites =
      (GeneralNominalCenteredSteps.install state original support).erased.current.sites := by
  change state.erased.current.sites ++ (GeneralNominalSharedEmission.emitted
      (GeneralNominalPacketReordering.rebase original.packet order pair)).sites = _
  rw [GeneralNominalPacketReordering.shared_emitted_sites order pair roleEq]
  rfl

theorem installed_edges (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration)
    (state : GeneralNominalCenteredSteps.State roles) (support) :
    (GeneralNominalCenteredSteps.install state (rebase original order pair) support).erased.current.edges =
      (GeneralNominalCenteredSteps.install state original support).erased.current.edges := by
  change state.erased.current.edges ++
    (GeneralNominalPacketReordering.rebase original.packet order pair).children.map _ = _
  rw [GeneralNominalPacketReordering.children]
  rfl

theorem installed_center_sites (order : Reorders original.packet.registry registry)
    (pair : DeclarationReorders original.packet.declaration declaration)
    (state : GeneralNominalCenteredSteps.State roles) (support) (site : Site roles) :
    site ∈ (GeneralNominalCenteredSteps.install state (rebase original order pair) support).sites ↔
      site ∈ (GeneralNominalCenteredSteps.install state original support).sites := by
  change site ∈ state.sites ++ (rebase original order pair).emitted ↔ site ∈ state.sites ++ original.emitted
  simp only [List.mem_append,emitted_mem]

end Yulang.GeneralNominalCenteredPlanReordering
