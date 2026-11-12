import Yulang.GeneralNominalAssociatedSourceTransport

/-! Actual nonterminal child emissions with bare-variable inputs and nominal
named output requests. Materialization does not discharge child Evidence. -/
namespace Yulang.GeneralNominalWhereAssociatedFacts
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralNominalLinearCaptureFacts GeneralNominalLinearMaterializationFacts
open GeneralNominalSharedCaptureFacts GeneralDeclarations CommonNominalFullCarrier
open GeneralNominalMaterialization GeneralDeclarationDemands

theorem input_requests_empty (input : InputRequest)
    (variableInput : ∃ name, GeneralDeclarationPatterns.normalize input.pattern = .var name) :
    inputRequests input = [] := by
  obtain ⟨name,eq⟩ := variableInput
  simp [inputRequests,eq]

theorem emission_requests (invocation : Nat) (declaration : Declaration) (clause : Clause)
    (valid : clause.Signature roles) (capture : GeneralDeclarationDemands.Capture)
    (allocation : Allocation roles clause)
    (variables : ∀ pattern ∈ clause.arguments, ∃ name, GeneralDeclarationPatterns.normalize pattern = .var name) :
    emissionRequests (emit invocation declaration clause valid capture allocation) =
      clause.outputs.map (fun equation =>
        (⟨equation.rhs,outputTarget declaration capture allocation.outputs equation,.actual⟩ : Request)) := by
  have empty : (emit invocation declaration clause valid capture allocation).inputs.flatMap inputRequests = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro input member
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
    apply input_requests_empty
    exact variables _ (List.getElem_mem _)
  unfold emissionRequests
  rw [empty,List.nil_append]
  simp only [emit,List.map_map]
  rfl

/-- Canonical source ordering retains the original clause and all concrete
allocation identities of every emitted child. -/
theorem canonical_emission_witness (invocation : Nat) (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration)
    (capture : GeneralDeclarationDemands.Capture)
    (allocate : (clause : Clause) → Allocation roles clause) (emission : Emission roles)
    (member : emission ∈ GeneralCanonicalChildOrder.canonicalEmit invocation declaration checked capture allocate) :
    ∃ clause, ∃ present : clause ∈ declaration.requirements,
      emission = emit invocation declaration clause (checked.signature.2.2.2 clause present) capture (allocate clause) := by
  have original := (GeneralCanonicalChildOrder.canonicalEmit_perm invocation declaration checked capture allocate).mem_iff.mpr member
  obtain ⟨clause,_,eq⟩ := List.mem_map.mp original
  exact ⟨clause.val,clause.property,eq.symm⟩

/-- Every materialization request is an actual root lookup or a named output of
an actual where clause. The latter keeps the real allocated output target. -/
theorem request_witness (state : GeneralNominalState.State) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (captures : GeneralNominalAllocation.Bindings)
    (variables : ∀ clause ∈ declaration.requirements, ∀ pattern ∈ clause.arguments,
      ∃ name, GeneralDeclarationPatterns.normalize pattern = .var name)
    (request : Request) (member : request ∈ requests state registry root declaration checked captures) :
    (∃ output ∈ root.demand.outputs, ∃ equation,
      declaration.associated.find? (fun e => e.name == output.name) = some equation ∧
      request = ⟨equation.rhs,output.target,.actual⟩) ∨
    (∃ clause ∈ declaration.requirements, ∃ equation ∈ clause.outputs,
      request = ⟨equation.rhs,outputTarget declaration
        (GeneralNominalAllocation.capture state registry root.identity declaration.id captures)
        (GeneralNominalAllocation.allocation (roles := roles) state registry root.identity declaration.id clause).outputs equation,.actual⟩) := by
  rcases List.mem_append.mp member with rootRequest | childRequest
  · obtain ⟨output,ho,equation,_,found,eq⟩ := GeneralNominalFiniteAssociatedFacts.root_request_witness declaration root request rootRequest
    exact Or.inl ⟨output,ho,equation,found,eq⟩
  · obtain ⟨emission,he,hr⟩ := List.mem_flatMap.mp childRequest
    obtain ⟨clause,hc,rfl⟩ := canonical_emission_witness root.identity declaration checked _ _ emission he
    rw [emission_requests _ _ _ _ _ _ (variables clause hc)] at hr
    obtain ⟨equation,hq,eq⟩ := List.mem_map.mp hr
    exact Or.inr ⟨clause,hc,equation,hq,eq.symm⟩
/-- Any finite associated declarations and demanded outputs. Nonempty where clauses are retained, with bare-variable inputs and named
nominal output requests. Every root and child output target is equivalent to the head. Source models, shared-binder coherence and allocation
merges suffice; generated materialization is a conclusion. -/
theorem generated_models (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (noOutputBinders : declaration.outputNames = [])
    (variables : ∀ clause ∈ declaration.requirements, ∀ pattern ∈ clause.arguments,
      ∃ name, GeneralDeclarationPatterns.normalize pattern = .var name)
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor) {n : Nat} (names : Fin n → Nat)
    (declared : ∀ i, names i ∈ declaration.inputNames)
    (bounds : Fin n → GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (translated : ∀ output ∈ root.demand.outputs, ∀ equation,
      declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate context.state.constructors context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (childTranslated : ∀ clause ∈ declaration.requirements, ∀ equation ∈ clause.outputs,
      GeneralNominalInspection.translate context.state.constructors context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
          .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (model : GeneralNominalCommonBridge.Assignment)
    (targets : ∀ output ∈ root.demand.outputs, Equivalent (model output.target).1
      (model (context.state.base.source slot)).1)
    (childTargets : ∀ clause ∈ declaration.requirements, ∀ equation ∈ clause.outputs,
      Equivalent (model (outputTarget declaration
        (GeneralNominalAllocation.capture context.state registry root.identity declaration.id
          (bindings context.state (report context declaration [(slot,slot)])))
        (GeneralNominalAllocation.allocation (roles := roles) context.state registry root.identity declaration.id clause).outputs equation)).1
        (model (context.state.base.source slot)).1)
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
    noOutputBinders slot descriptor recorded names declared bounds parameters
    model models coherent (by simpa only [calculated] using merges)
  unfold GeneralNominalRecursiveCandidates.generated
  apply GeneralNominalAssociatedSourceTransport.generated_models_transport context declaration _ _ slot
    descriptor.declaration.name names _ ?_ model ?_
  · simpa only [calculated] using base
  · intro request member
    rcases request_witness context.state registry root declaration checked _ variables request member with rootCase | childCase
    · obtain ⟨output,ho,equation,found,rfl⟩ := rootCase
      exact translated output ho equation found
    · obtain ⟨clause,hc,equation,he,rfl⟩ := childCase
      exact childTranslated clause hc equation he
  · intro request member
    rcases request_witness context.state registry root declaration checked _ variables request member with rootCase | childCase
    · obtain ⟨output,ho,equation,_,rfl⟩ := rootCase
      exact targets output ho
    · obtain ⟨clause,hc,equation,he,rfl⟩ := childCase
      exact childTargets clause hc equation he

/-- Finite associated-output variant of the exact branch residual. -/
theorem branch_models_iff (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (noOutputBinders : declaration.outputNames = [])
    (variables : ∀ clause ∈ declaration.requirements, ∀ pattern ∈ clause.arguments,
      ∃ name, GeneralDeclarationPatterns.normalize pattern = .var name)
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor) {n : Nat} (names : Fin n → Nat)
    (declared : ∀ i, names i ∈ declaration.inputNames)
    (bounds : Fin n → GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (translated : ∀ output ∈ root.demand.outputs, ∀ equation,
      declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate context.state.constructors context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (childTranslated : ∀ clause ∈ declaration.requirements, ∀ equation ∈ clause.outputs,
      GeneralNominalInspection.translate context.state.constructors context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
          .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (model : GeneralNominalCommonBridge.Assignment)
    (targets : ∀ output ∈ root.demand.outputs, Equivalent (model output.target).1
      (model (context.state.base.source slot)).1)
    (childTargets : ∀ clause ∈ declaration.requirements, ∀ equation ∈ clause.outputs,
      Equivalent (model (outputTarget declaration
        (GeneralNominalAllocation.capture context.state registry root.identity declaration.id
          (bindings context.state (report context declaration [(slot,slot)])))
        (GeneralNominalAllocation.allocation (roles := roles) context.state registry root.identity declaration.id clause).outputs equation)).1
        (model (context.state.base.source slot)).1) :
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
    exact ⟨models,coherent,merges,generated_models context registry root declaration checked noOutputBinders variables
      slot descriptor recorded names declared bounds parameters query translated childTranslated model targets childTargets models coherent merges⟩

/-- The nominal shape also discharges the syntactic deferred-expression flag;
it does not manufacture definitions for unknown demanded associated names. -/
theorem generated_unknown_false (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (variables : ∀ clause ∈ declaration.requirements, ∀ pattern ∈ clause.arguments,
      ∃ name, GeneralDeclarationPatterns.normalize pattern = .var name)
    (headBounds : List (GeneralNominalInspection.Bounds context.state))
    (name : Nat) {n : Nat} (names : Fin n → Nat)
    (translated : ∀ output ∈ root.demand.outputs, ∀ equation,
      declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate context.state.constructors context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
          .nominal name (List.ofFn fun i => .variables [names i]))
    (childTranslated : ∀ clause ∈ declaration.requirements, ∀ equation ∈ clause.outputs,
      GeneralNominalInspection.translate context.state.constructors context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
          .nominal name (List.ofFn fun i => .variables [names i])) :
    (GeneralNominalRecursiveCandidates.generated registry context root declaration checked headBounds).unknown = false := by
  unfold GeneralNominalRecursiveCandidates.generated
  have each : ∀ r ∈ requests context.state registry root declaration checked
      (bindings context.state (report context declaration headBounds)),
      (schema (GeneralNominalInspection.translate context.state.constructors context.interpretation
        (GeneralDeclarationPatterns.normalize r.pattern)) (.source r.target) r.mode).unknown = false := by
    intro r hr
    rcases request_witness context.state registry root declaration checked _ variables r hr with rootCase | childCase
    · obtain ⟨output,ho,equation,found,rfl⟩ := rootCase
      rw [translated output ho equation found,GeneralNominalAssociatedSourceTransport.schema_source_exact]
    · obtain ⟨clause,hc,equation,he,rfl⟩ := childCase
      rw [childTranslated clause hc equation he,GeneralNominalAssociatedSourceTransport.schema_source_exact]
  unfold GeneralNominalMaterialization.generated
  have fold (ss : List Schema) (known : ∀ s ∈ ss, s.unknown = false) :
      (ss.foldr Schema.append {}).unknown = false := by
    induction ss with
    | nil => rfl
    | cons s rest ih =>
      simp only [List.foldr_cons,Schema.append,known s (by simp),Bool.false_or]
      exact ih (fun x hx => known x (by simp [hx]))
  apply fold
  intro s hs
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hs
  exact each r hr

/-- In this finite nominal-output fragment, the remaining readiness condition
is exactly definedness of each demanded associated name. -/
theorem request_ready_iff (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (variables : ∀ clause ∈ declaration.requirements, ∀ pattern ∈ clause.arguments,
      ∃ name, GeneralDeclarationPatterns.normalize pattern = .var name)
    (headBounds : List (GeneralNominalInspection.Bounds context.state))
    (name : Nat) {n : Nat} (names : Fin n → Nat)
    (translated : ∀ output ∈ root.demand.outputs, ∀ equation,
      declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate context.state.constructors context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
          .nominal name (List.ofFn fun i => .variables [names i]))
    (childTranslated : ∀ clause ∈ declaration.requirements, ∀ equation ∈ clause.outputs,
      GeneralNominalInspection.translate context.state.constructors context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
          .nominal name (List.ofFn fun i => .variables [names i])) :
    RequestReady registry context root declaration checked headBounds ↔ RootDefined declaration root := by
  exact and_iff_left (generated_unknown_false context registry root declaration checked variables headBounds name names translated childTranslated)
end Yulang.GeneralNominalWhereAssociatedFacts
