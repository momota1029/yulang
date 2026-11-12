import Yulang.GeneralNominalLinearCaptureFacts

/-! Actual materialization of a linear nominal head at its already constrained
source identity. This does not assert equations at unrelated output sources. -/
namespace Yulang.GeneralNominalLinearMaterializationFacts
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDeclarations CommonNominalFullCarrier
open GeneralNominalLinearCaptureFacts

 theorem schemas_exact {n : Nat} (names : Fin n → Nat) (origins : Nat → Origin)
    (mode : GeneralNominalMaterialization.Mode) (offset : Nat) :
    GeneralNominalMaterialization.schemas (List.ofFn fun i => .variables [names i]) origins mode offset =
      { variables := List.ofFn fun i => ⟨names i,origins (offset+i.val),mode⟩ } := by
  induction n generalizing offset with
  | zero => simp [List.ofFn_zero,GeneralNominalMaterialization.schemas]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema]
    rw [ih]
    simp [List.ofFn_succ,GeneralNominalMaterialization.Schema.append,Nat.add_comm,Nat.add_left_comm]

def headSchema (state : GeneralNominalState.State) (slot : Fin state.base.slots)
    (name : Nat) {n : Nat} (names : Fin n → Nat) : GeneralNominalMaterialization.Schema where
  variables := List.ofFn fun i => ⟨names i,.nominal (.source (state.base.source slot)) name i.val,.actual⟩
  tests := [(.source (state.base.source slot),.nominal name n)]

theorem schema_exact (state : GeneralNominalState.State) (slot : Fin state.base.slots)
    (name : Nat) {n : Nat} (names : Fin n → Nat) (mode : GeneralNominalMaterialization.Mode) :
    GeneralNominalMaterialization.schema (.nominal name (List.ofFn fun i => .variables [names i]))
      (.source (state.base.source slot)) mode = headSchema state slot name names := by
  simp [GeneralNominalMaterialization.schema,schemas_exact,headSchema]

theorem fitsAll_length (state : GeneralSourceState.State) (model : GeneralNominalCommonBridge.Assignment)
    (parameters : List (GeneralNominalState.Parameter state.slots)) (values : List Argument)
    (fits : GeneralNominalState.FitsAll state model parameters values) : values.length = parameters.length := by
  induction fits with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem schema_models (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (noOutputBinders : declaration.outputNames = [])
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor) {n : Nat}
    (names : Fin n → Nat) (distinct : Function.Injective names)
    (bounds : Fin n → GeneralNominalInspection.Bounds state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models state model) :
    GeneralNominalMaterialization.Models state declaration
      (GeneralNominalAllocation.capture state registry invocation declaration.id
        (bindings state (captured state slot descriptor.declaration.name names bounds)))
      (captured state slot descriptor.declaration.name names bounds)
      (headSchema state slot descriptor.declaration.name names) model := by
  have arg (i : Fin n) := nominal_argument_bounds state model models slot descriptor recorded i.val (bounds i)
    (by rw [parameters]; simp [i.isLt])
  have capture (i : Fin n) :
      (GeneralNominalAllocation.capture state registry invocation declaration.id
        (bindings state (captured state slot descriptor.declaration.name names bounds))).inputs (names i) =
        (state.base.source (bounds i).1,state.base.source (bounds i).2) := by
    simp only [bindings,captured,variablesReport,List.map_ofFn,Function.comp_def,GeneralNominalAllocation.capture]
    rw [occurrences_exact state names distinct bounds i]
  refine ⟨?_,?_,?_,?_⟩
  · intro test member
    have eq := List.mem_singleton.mp member
    subst test
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observed
    cases observed
    obtain ⟨values,fits,equal⟩ := models.2.1 slot descriptor recorded
    refine ⟨values,?_,equal⟩
    rw [fitsAll_length state.base model descriptor.arguments values fits,parameters]
    exact List.length_ofFn
  · intro entry member
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
    refine ⟨(arg i).1,?_⟩
    intro actual observed
    simp only [GeneralNominalMaterialization.VariableHolds,noOutputBinders,List.not_mem_nil,↓reduceIte]
    rw [capture]
    exact (arg i).2 actual observed
  · intro first ha last hb same _ _ a b ha' hb'
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    have eq := distinct same
    subst j
    exact nominal_observation_unique model
      (.argument (.source (state.base.source slot)) descriptor.declaration.name i.val) a b ha' hb'
  · intro entry ha capture hb same _ origin found a b ha' hb'
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    have eq := distinct same
    subst j
    cases Option.some.inj found
    exact nominal_observation_unique model
      (.argument (.source (state.base.source slot)) descriptor.declaration.name i.val) a b ha'
      (by simpa only [Nat.zero_add,embed] using hb')

/-- A checked declaration without where clauses has no produced output-only
binders. Associated equations themselves may still be nonempty. -/
theorem no_output_binders (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration)
    (terminal : declaration.requirements = []) : declaration.outputNames = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name member
  obtain ⟨binder,present,_⟩ := List.mem_map.mp member
  obtain ⟨clause,visible,_⟩ := checked.produced binder present
  rw [terminal] at visible
  cases visible

theorem root_requests_exact (state : GeneralNominalState.State) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (captures : GeneralNominalAllocation.Bindings)
    (terminal : declaration.requirements = []) (equation : Equation)
    (associated : declaration.associated = [equation]) (slot : Fin state.base.slots)
    (output : root.demand.outputs = [⟨equation.name,state.base.source slot⟩]) :
    GeneralNominalMaterialization.requests state registry root declaration checked captures =
      [⟨equation.rhs,state.base.source slot,.actual⟩] := by
  simp [GeneralNominalMaterialization.requests,GeneralNominalMaterialization.rootRequests,
    output,associated,GeneralCanonicalChildOrder.canonicalEmit,GeneralDeclarationDemands.emitAll,
    GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,terminal]

theorem generated_exact (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (terminal : declaration.requirements = []) (equation : Equation)
    (associated : declaration.associated = [equation]) (slot : Fin context.state.base.slots)
    (output : root.demand.outputs = [⟨equation.name,context.state.base.source slot⟩])
    (name : Nat) {n : Nat} (names : Fin n → Nat)
    (translated : GeneralNominalInspection.translate context.state.constructors context.interpretation
      (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal name (List.ofFn fun i => .variables [names i]))
    (headBounds : List (GeneralNominalInspection.Bounds context.state)) :
    generated registry context root declaration checked headBounds = headSchema context.state slot name names := by
  unfold generated
  rw [root_requests_exact context.state registry root declaration checked _ terminal equation associated slot output]
  simp [GeneralNominalMaterialization.generated,translated,schema_exact,headSchema,
    GeneralNominalMaterialization.Schema.append]

/-- A nonempty associated nominal output request at the already constrained
head source is realized in every original model. Unlike an arbitrary output
identity, it needs no new output equality premise and no branch witness. -/
theorem branch_models (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (terminal : declaration.requirements = []) (equation : Equation)
    (associated : declaration.associated = [equation])
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor) {n : Nat}
    (names : Fin n → Nat) (distinct : Function.Injective names)
    (inputs : declaration.inputNames = List.ofFn names)
    (bounds : Fin n → GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (output : root.demand.outputs = [⟨equation.name,context.state.base.source slot⟩])
    (translated : GeneralNominalInspection.translate context.state.constructors context.interpretation
      (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models context.state model) :
    BranchModels registry context root declaration checked [(slot,slot)] model := by
  have head := private_models context registry root declaration slot descriptor recorded names distinct
    inputs bounds parameters query model models
  refine ⟨head.1,head.2,?_⟩
  rw [generated_exact context registry root declaration checked terminal equation associated slot output
    descriptor.declaration.name names translated]
  rw [report_exact context declaration slot descriptor recorded names bounds parameters query]
  exact schema_models context.state registry root.identity declaration (no_output_binders declaration checked terminal)
    slot descriptor recorded names distinct bounds parameters model models
end Yulang.GeneralNominalLinearMaterializationFacts
