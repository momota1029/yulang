import Yulang.GeneralNominalSharedCaptureFacts
import Yulang.GeneralNominalLinearMaterializationFacts

/-! Materialization for arbitrary finite sharing at the same nominal head.
The independent source-model, observed-coherence and allocation-equation
obligations are retained; generated materialization itself is derived. -/
namespace Yulang.GeneralNominalSharedMaterializationFacts
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralNominalLinearCaptureFacts GeneralNominalLinearMaterializationFacts
open GeneralNominalSharedCaptureFacts GeneralDeclarations CommonNominalFullCarrier

theorem occurrence_iff (state : GeneralNominalState.State) (slot : Fin state.base.slots)
    (head : Nat) {n : Nat} (names : Fin n → Nat)
    (bounds : Fin n → GeneralNominalInspection.Bounds state) (name : Nat) (pair : Nat × Nat) :
    pair ∈ GeneralNominalAllocation.occurrences
      (bindings state (captured state slot head names bounds)) name ↔
      ∃ j, names j = name ∧ (state.base.source (bounds j).1,state.base.source (bounds j).2) = pair := by
  simp only [GeneralNominalAllocation.occurrences,bindings,captured,variablesReport,
    List.map_ofFn,Function.comp_def]
  constructor
  · intro member
    obtain ⟨entry,member,equal⟩ := List.mem_map.mp member
    obtain ⟨member,kept⟩ := List.mem_filter.mp member
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
    exact ⟨j,of_decide_eq_true kept,equal⟩
  · rintro ⟨j,same,rfl⟩
    apply List.mem_map.mpr
    refine ⟨_,List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨j,rfl⟩,?_⟩,rfl⟩
    simp [same]

theorem schema_models (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (noOutputBinders : declaration.outputNames = [])
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor) {n : Nat} (names : Fin n → Nat)
    (declared : ∀ i, names i ∈ declaration.inputNames)
    (bounds : Fin n → GeneralNominalInspection.Bounds state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models state model)
    (coherent : Coherent model (state.base.source slot) descriptor.declaration.name names)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges state registry invocation declaration
        (bindings state (captured state slot descriptor.declaration.name names bounds)))) :
    GeneralNominalMaterialization.Models state declaration
      (GeneralNominalAllocation.capture state registry invocation declaration.id
        (bindings state (captured state slot descriptor.declaration.name names bounds)))
      (captured state slot descriptor.declaration.name names bounds)
      (headSchema state slot descriptor.declaration.name names) model := by
  have arg (i : Fin n) := nominal_argument_bounds state model models slot descriptor recorded i.val (bounds i)
    (by rw [parameters]; simp [i.isLt])
  have fits (i : Fin n) (actual : Ty)
      (seen : Observes model (.nominal (.source (state.base.source slot)) descriptor.declaration.name i.val) actual) :
      GeneralNominalCaptureMerges.Fits model
        ((GeneralNominalAllocation.capture state registry invocation declaration.id
          (bindings state (captured state slot descriptor.declaration.name names bounds))).inputs (names i)) actual := by
    have member : (state.base.source (bounds i).1,state.base.source (bounds i).2) ∈
        GeneralNominalAllocation.occurrences
          (bindings state (captured state slot descriptor.declaration.name names bounds)) (names i) :=
      (occurrence_iff state slot descriptor.declaration.name names bounds (names i) _).mpr ⟨i,rfl,rfl⟩
    have nonempty : GeneralNominalAllocation.occurrences
        (bindings state (captured state slot descriptor.declaration.name names bounds)) (names i) ≠ [] := by
      intro empty; rw [empty] at member; cases member
    apply (GeneralNominalCaptureMerges.capture_interval_exact state registry invocation declaration _ model
      merges (names i) (declared i) nonempty actual).mpr
    intro pair present
    obtain ⟨j,same,rfl⟩ := (occurrence_iff state slot descriptor.declaration.name names bounds (names i) pair).mp present
    obtain ⟨other,observed⟩ := (arg j).1
    have fit := (arg j).2 other observed
    have equal := coherent i j same.symm actual other seen observed
    exact ⟨subtype_trans fit.1 equal.2,subtype_trans equal.1 fit.2⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro test member
    have eq := List.mem_singleton.mp member
    subst test
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observed
    cases observed
    obtain ⟨values,fit,equal⟩ := models.2.1 slot descriptor recorded
    refine ⟨values,?_,equal⟩
    rw [fitsAll_length state.base model descriptor.arguments values fit,parameters]
    exact List.length_ofFn
  · intro entry member
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
    refine ⟨(arg i).1,?_⟩
    intro actual observed
    simpa [GeneralNominalMaterialization.VariableHolds,noOutputBinders] using fits i actual observed
  · intro first ha last hb same _ _ a b ha' hb'
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    exact coherent i j same a b ha' hb'
  · intro entry ha capture hb same _ origin found a b ha' hb'
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    cases Option.some.inj found
    exact coherent i j same a b ha' (by simpa only [Nat.zero_add,embed] using hb')

/-- Arbitrary finite repeated names, terminal checked declaration, and a
single associated output at the constrained head source. Only coherence and
allocation merge equations remain beyond the original source model. -/
theorem branch_models_iff (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (terminal : declaration.requirements = []) (equation : Equation)
    (associated : declaration.associated = [equation])
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor) {n : Nat} (names : Fin n → Nat)
    (declared : ∀ i, names i ∈ declaration.inputNames)
    (bounds : Fin n → GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (output : root.demand.outputs = [⟨equation.name,context.state.base.source slot⟩])
    (translated : GeneralNominalInspection.translate context.state.constructors context.interpretation
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
    refine ⟨models,coherent,merges,?_⟩
    rw [generated_exact context registry root declaration checked terminal equation associated slot output
      descriptor.declaration.name names translated]
    have calculated := report_exact context declaration slot descriptor recorded names bounds parameters query
    rw [calculated] at merges ⊢
    exact schema_models context.state registry root.identity declaration
      (no_output_binders declaration checked terminal) slot descriptor recorded names declared bounds parameters
      model models coherent merges
end Yulang.GeneralNominalSharedMaterializationFacts
