import Yulang.GeneralNominalFiniteAssociatedFacts

/-! Materialization at distinct nominal output source identities whose actual
values are equivalent to the inspected head. -/
namespace Yulang.GeneralNominalAssociatedSourceTransport
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralNominalLinearCaptureFacts GeneralNominalLinearMaterializationFacts
open GeneralNominalSharedCaptureFacts GeneralDeclarations CommonNominalFullCarrier
open GeneralNominalMaterialization

theorem nominal_source_transport (model : GeneralNominalCommonBridge.Assignment)
    (first last name index : Nat)
    (equal : Equivalent (model first).1 (model last).1) (actual : Ty)
    (seen : Observes model (.nominal (.source first) name index) actual) :
    Observes model (.nominal (.source last) name index) actual := by
  cases seen with
  | nominal parent eq found =>
    cases parent
    exact .nominal (.source last) ⟨subtype_trans equal.2 eq.1,subtype_trans eq.2 equal.1⟩ found

theorem schema_source_exact (target name : Nat) {n : Nat} (names : Fin n → Nat) (mode : Mode) :
    schema (.nominal name (List.ofFn fun i => .variables [names i])) (.source target) mode =
      { variables := List.ofFn fun i => ⟨names i,.nominal (.source target) name i.val,.actual⟩,
        tests := [(.source target,.nominal name n)] } := by
  simp [schema,schemas_exact]

theorem fold_variables (ss : List Schema) (entry : Use)
    (member : entry ∈ (ss.foldr Schema.append {}).variables) :
    ∃ s ∈ ss, entry ∈ s.variables := by
  induction ss with
  | nil => simp at member
  | cons s rest ih =>
    simp only [List.foldr_cons,Schema.append,List.mem_append] at member
    rcases member with head | tail
    · exact ⟨s,by simp,head⟩
    · obtain ⟨t,ht,hv⟩ := ih tail
      exact ⟨t,by simp [ht],hv⟩

theorem fold_tests (ss : List Schema) (test : Origin × Test)
    (member : test ∈ (ss.foldr Schema.append {}).tests) :
    ∃ s ∈ ss, test ∈ s.tests := by
  induction ss with
  | nil => simp at member
  | cons s rest ih =>
    simp only [List.foldr_cons,Schema.append,List.mem_append] at member
    rcases member with head | tail
    · exact ⟨s,by simp,head⟩
    · obtain ⟨t,ht,hv⟩ := ih tail
      exact ⟨t,by simp [ht],hv⟩

theorem generated_models_transport (context : Context) (declaration : Declaration)
    (capture : GeneralDeclarationDemands.Capture) (report : Report context.state)
    (slot : Fin context.state.base.slots) (name : Nat) {n : Nat} (names : Fin n → Nat)
    (requests : List Request)
    (translated : ∀ r ∈ requests,
      GeneralNominalInspection.translate context.state.constructors context.interpretation
        (GeneralDeclarationPatterns.normalize r.pattern) =
          .nominal name (List.ofFn fun i => .variables [names i]))
    (model : GeneralNominalCommonBridge.Assignment)
    (targets : ∀ r ∈ requests, Equivalent (model r.target).1 (model (context.state.base.source slot)).1)
    (base : Models context.state declaration capture report (headSchema context.state slot name names) model) :
    Models context.state declaration capture report
      (GeneralNominalMaterialization.generated context.state context.interpretation requests) model := by
  have variableWitness (v : Use)
      (hv : v ∈ (GeneralNominalMaterialization.generated context.state context.interpretation requests).variables) :
      ∃ r ∈ requests, ∃ i : Fin n, v = ⟨names i,.nominal (.source r.target) name i.val,.actual⟩ := by
    obtain ⟨s,hs,hv⟩ := fold_variables _ v hv
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hs
    rw [translated r hr,schema_source_exact] at hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    exact ⟨r,hr,i,rfl⟩
  have baseMember (i : Fin n) :
      (⟨names i,.nominal (.source (context.state.base.source slot)) name i.val,.actual⟩ : Use) ∈
      (headSchema context.state slot name names).variables := by
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro t ht
    obtain ⟨s,hs,ht⟩ := fold_tests _ t ht
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hs
    rw [translated r hr,schema_source_exact] at ht
    have eq := List.mem_singleton.mp ht
    subst t
    refine ⟨⟨_,.source r.target⟩,?_⟩
    intro actual seen
    cases seen
    have original := (base.1 (.source (context.state.base.source slot),.nominal name n) (by simp [headSchema])).2
      _ (.source (context.state.base.source slot))
    obtain ⟨arguments,length,equal⟩ := original
    exact ⟨arguments,length,subtype_trans (targets r hr).1 equal.1,subtype_trans equal.2 (targets r hr).2⟩
  · intro v hv
    obtain ⟨r,hr,i,rfl⟩ := variableWitness v hv
    have prior := base.2.1 _ (baseMember i)
    constructor
    · obtain ⟨a,seen⟩ := prior.1
      exact ⟨a,nominal_source_transport model _ _ name i.val ⟨(targets r hr).2,(targets r hr).1⟩ a seen⟩
    · intro a seen
      exact prior.2 a (nominal_source_transport model _ _ name i.val (targets r hr) a seen)
  · intro first hf last hl same _ _ a b ha hb
    obtain ⟨r,hr,i,rfl⟩ := variableWitness first hf
    obtain ⟨s,hs,j,rfl⟩ := variableWitness last hl
    exact base.2.2.1 _ (baseMember i) _ (baseMember j) same rfl rfl a b
      (nominal_source_transport model _ _ name i.val (targets r hr) a ha)
      (nominal_source_transport model _ _ name j.val (targets s hs) b hb)
  · intro v hv c hc same _ origin found a b ha hb
    obtain ⟨r,hr,i,rfl⟩ := variableWitness v hv
    exact base.2.2.2 _ (baseMember i) c hc same rfl origin found a b
      (nominal_source_transport model _ _ name i.val (targets r hr) a ha) hb
/-- Any finite associated declarations and demanded outputs. Every actual
requested target is equivalent to the inspected head and every selected associated RHS has the same
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
    (translated : ∀ output ∈ root.demand.outputs, ∀ equation,
      declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate context.state.constructors context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (model : GeneralNominalCommonBridge.Assignment)
    (targets : ∀ output ∈ root.demand.outputs, Equivalent (model output.target).1
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
    (no_output_binders declaration checked terminal) slot descriptor recorded names declared bounds parameters
    model models coherent (by simpa only [calculated] using merges)
  unfold GeneralNominalRecursiveCandidates.generated
  rw [GeneralNominalFiniteAssociatedFacts.terminal_requests context.state registry root declaration checked _ terminal]
  apply generated_models_transport context declaration _ _ slot descriptor.declaration.name names _ ?_ model ?_
  · simpa only [calculated] using base
  · intro request member
    obtain ⟨output,ho,equation,_,found,rfl⟩ := GeneralNominalFiniteAssociatedFacts.root_request_witness declaration root request member
    exact translated output ho equation found
  · intro request member
    obtain ⟨output,ho,equation,_,_,rfl⟩ := GeneralNominalFiniteAssociatedFacts.root_request_witness declaration root request member
    exact targets output ho

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
    (translated : ∀ output ∈ root.demand.outputs, ∀ equation,
      declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate context.state.constructors context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (model : GeneralNominalCommonBridge.Assignment)
    (targets : ∀ output ∈ root.demand.outputs, Equivalent (model output.target).1
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
    exact ⟨models,coherent,merges,generated_models context registry root declaration checked terminal
      slot descriptor recorded names declared bounds parameters query translated model targets models coherent merges⟩

/-- The nominal shape also discharges the syntactic deferred-expression flag;
it does not manufacture definitions for unknown demanded associated names. -/
theorem generated_unknown_false (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (terminal : declaration.requirements = [])
    (headBounds : List (GeneralNominalInspection.Bounds context.state))
    (name : Nat) {n : Nat} (names : Fin n → Nat)
    (translated : ∀ output ∈ root.demand.outputs, ∀ equation,
      declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate context.state.constructors context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
          .nominal name (List.ofFn fun i => .variables [names i])) :
    (GeneralNominalRecursiveCandidates.generated registry context root declaration checked headBounds).unknown = false := by
  unfold GeneralNominalRecursiveCandidates.generated
  rw [GeneralNominalFiniteAssociatedFacts.terminal_requests context.state registry root declaration checked _ terminal]
  have each : ∀ r ∈ rootRequests declaration root,
      (schema (GeneralNominalInspection.translate context.state.constructors context.interpretation
        (GeneralDeclarationPatterns.normalize r.pattern)) (.source r.target) r.mode).unknown = false := by
    intro r hr
    obtain ⟨output,ho,equation,_,found,rfl⟩ := GeneralNominalFiniteAssociatedFacts.root_request_witness declaration root r hr
    rw [translated output ho equation found,schema_source_exact]
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
    (terminal : declaration.requirements = [])
    (headBounds : List (GeneralNominalInspection.Bounds context.state))
    (name : Nat) {n : Nat} (names : Fin n → Nat)
    (translated : ∀ output ∈ root.demand.outputs, ∀ equation,
      declaration.associated.find? (fun e => e.name == output.name) = some equation →
      GeneralNominalInspection.translate context.state.constructors context.interpretation
        (GeneralDeclarationPatterns.normalize equation.rhs) =
          .nominal name (List.ofFn fun i => .variables [names i])) :
    RequestReady registry context root declaration checked headBounds ↔ RootDefined declaration root := by
  exact and_iff_left (generated_unknown_false context registry root declaration checked terminal headBounds name names translated)
end Yulang.GeneralNominalAssociatedSourceTransport
