import Yulang.GeneralNominalSharedMaterializationFacts

/-! Arbitrary finite lists of associated outputs at the inspected nominal head.
The generated schema is derived from actual requests, not assumed valid. -/
namespace Yulang.GeneralNominalFiniteAssociatedFacts
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralNominalLinearCaptureFacts GeneralNominalLinearMaterializationFacts
open GeneralNominalSharedCaptureFacts GeneralDeclarations CommonNominalFullCarrier
open GeneralNominalMaterialization

theorem models_of_membership (state : GeneralNominalState.State) (declaration : Declaration)
    (capture : GeneralDeclarationDemands.Capture) (report : Report state) (large small : Schema)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models state declaration capture report large model)
    (tests : ∀ t ∈ small.tests, t ∈ large.tests)
    (variables : ∀ v ∈ small.variables, v ∈ large.variables) :
    Models state declaration capture report small model := by
  refine ⟨?_,?_,?_,?_⟩
  · intro t ht; exact valid.1 t (tests t ht)
  · intro v hv; exact valid.2.1 v (variables v hv)
  · intro a ha b hb; exact valid.2.2.1 a (variables a ha) b (variables b hb)
  · intro a ha; exact valid.2.2.2 a (variables a ha)

theorem fold_membership (schemas : List Schema) (large : Schema)
    (tests : ∀ s ∈ schemas, ∀ t ∈ s.tests, t ∈ large.tests)
    (variables : ∀ s ∈ schemas, ∀ v ∈ s.variables, v ∈ large.variables) :
    (∀ t ∈ (schemas.foldr Schema.append {}).tests, t ∈ large.tests) ∧
    (∀ v ∈ (schemas.foldr Schema.append {}).variables, v ∈ large.variables) := by
  induction schemas with
  | nil => simp
  | cons s rest ih =>
    have tail := ih (fun x hx => tests x (by simp [hx])) (fun x hx => variables x (by simp [hx]))
    constructor
    · intro t ht
      simp only [List.foldr_cons,Schema.append,List.mem_append] at ht
      exact ht.elim (tests s (by simp) t) (tail.1 t)
    · intro v hv
      simp only [List.foldr_cons,Schema.append,List.mem_append] at hv
      exact hv.elim (variables s (by simp) v) (tail.2 v)

theorem generated_models_of_same_schema (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation)
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture) (report : Report state)
    (requests : List Request) (large : Schema)
    (same : ∀ request ∈ requests,
      schema (GeneralNominalInspection.translate state.constructors interpretation
        (GeneralDeclarationPatterns.normalize request.pattern)) (.source request.target) request.mode = large)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models state declaration capture report large model) :
    Models state declaration capture report (GeneralNominalMaterialization.generated state interpretation requests) model := by
  apply models_of_membership state declaration capture report large _ model valid
  · apply (fold_membership _ large ?_ ?_).1
    · intro s hs t ht
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hs
      simpa only [same r hr] using ht
    · intro s hs v hv
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hs
      simpa only [same r hr] using hv
  · apply (fold_membership _ large ?_ ?_).2
    · intro s hs t ht
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hs
      simpa only [same r hr] using ht
    · intro s hs v hv
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hs
      simpa only [same r hr] using hv

/-- Requests actually emitted by the root lookup retain their selected equation
and requested target. No singleton or ordering hypothesis is used. -/
theorem root_request_witness (declaration : Declaration)
    (root : GeneralSourceDictionaries.Occurrence roles) (request : Request)
    (member : request ∈ rootRequests declaration root) :
    ∃ output ∈ root.demand.outputs, ∃ equation ∈ declaration.associated,
      declaration.associated.find? (fun e => e.name == output.name) = some equation ∧
      request = ⟨equation.rhs,output.target,.actual⟩ := by
  obtain ⟨output,ho,hr⟩ := List.mem_flatMap.mp member
  obtain ⟨equation,he,eq⟩ := List.mem_map.mp hr
  have found : declaration.associated.find? (fun equation => equation.name == output.name) = some equation := by
    simpa using he
  exact ⟨output,ho,equation,List.mem_of_find?_eq_some found,found,eq.symm⟩

theorem terminal_requests (state : GeneralNominalState.State) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (captures : GeneralNominalAllocation.Bindings)
    (terminal : declaration.requirements = []) :
    requests state registry root declaration checked captures = rootRequests declaration root := by
  simp [requests,GeneralCanonicalChildOrder.canonicalEmit,GeneralDeclarationDemands.emitAll,
    GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,terminal]

/-- Any finite associated declarations and demanded outputs. Every actual
requested target is the inspected head and every selected associated RHS has the same
nominal binder query. Source models, shared-binder coherence and allocation
merges suffice; generated materialization is a conclusion. -/
theorem generated_models (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (terminal : declaration.requirements = [])
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor) {n : Nat} (names : Fin n → Nat)
    (declared : ∀ i, names i ∈ declaration.inputNames)
    (bounds : Fin n → GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (outputs : ∀ output ∈ root.demand.outputs, output.target = context.state.base.source slot)
    (translated : ∀ output ∈ root.demand.outputs, ∀ equation,
      declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate context.state.constructors context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (model : GeneralNominalCommonBridge.Assignment)
    (models : GeneralNominalState.Models context.state model)
    (coherent : Coherent model (context.state.base.source slot) descriptor.declaration.name names)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges context.state registry root.identity declaration
        (bindings context.state (report context declaration [(slot,slot)])))) :
    Models context.state declaration
      (GeneralNominalAllocation.capture context.state registry root.identity declaration.id
        (bindings context.state (report context declaration [(slot,slot)])))
      (report context declaration [(slot,slot)])
      (GeneralNominalRecursiveCandidates.generated registry context root declaration checked [(slot,slot)]) model := by
  have calculated := report_exact context declaration slot descriptor recorded names bounds parameters query
  have base := GeneralNominalSharedMaterializationFacts.schema_models context.state registry root.identity declaration
    (no_output_binders declaration checked terminal) slot descriptor recorded names declared bounds parameters
    model models coherent (by simpa only [calculated] using merges)
  unfold GeneralNominalRecursiveCandidates.generated
  rw [terminal_requests context.state registry root declaration checked _ terminal]
  apply generated_models_of_same_schema context.state context.interpretation declaration _ _ _
    (headSchema context.state slot descriptor.declaration.name names) ?_ model
  · simpa only [calculated] using base
  · intro request member
    obtain ⟨output,ho,equation,_,found,rfl⟩ := root_request_witness declaration root request member
    rw [outputs output ho,translated output ho equation found]
    exact schema_exact context.state slot descriptor.declaration.name names .actual

/-- Finite associated-output variant of the exact branch residual. -/
theorem branch_models_iff (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (terminal : declaration.requirements = [])
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor) {n : Nat} (names : Fin n → Nat)
    (declared : ∀ i, names i ∈ declaration.inputNames)
    (bounds : Fin n → GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (outputs : ∀ output ∈ root.demand.outputs, output.target = context.state.base.source slot)
    (translated : ∀ output ∈ root.demand.outputs, ∀ equation,
      declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate context.state.constructors context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (model : GeneralNominalCommonBridge.Assignment) :
    BranchModels registry context root declaration checked [(slot,slot)] model ↔
      GeneralNominalState.Models context.state model ∧
      Coherent model (context.state.base.source slot) descriptor.declaration.name names ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalAllocation.merges context.state registry root.identity declaration
          (bindings context.state (report context declaration [(slot,slot)]))) := by
  rw [branch_models_iff_residual context registry root declaration checked slot descriptor recorded
    names bounds parameters query model]
  constructor
  · rintro ⟨models,coherent,merges,_⟩
    exact ⟨models,coherent,merges⟩
  · rintro ⟨models,coherent,merges⟩
    exact ⟨models,coherent,merges,generated_models context registry root declaration checked terminal
      slot descriptor recorded names declared bounds parameters query outputs translated model models coherent merges⟩
end Yulang.GeneralNominalFiniteAssociatedFacts
