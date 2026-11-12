import Yulang.GeneralNominalLinearCaptureFacts

/-! Arbitrary finite binder sharing under one nominal head. Observed equality
is required only for positions with the same name; private allocation equations
remain an explicit, separate obligation in the unchanged assignment. -/
namespace Yulang.GeneralNominalSharedCaptureFacts
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralNominalLinearCaptureFacts GeneralDeclarations CommonNominalFullCarrier

/-- Semantic agreement at all repeated names, not syntactic injectivity. -/
def Coherent (model : GeneralNominalCommonBridge.Assignment) (source name : Nat)
    {n : Nat} (names : Fin n → Nat) : Prop :=
  ∀ i j, names i = names j → ∀ a b,
    Observes model (.nominal (.source source) name i.val) a →
    Observes model (.nominal (.source source) name j.val) b → Equivalent a b

theorem coherent_of_injective (model : GeneralNominalCommonBridge.Assignment) (source name : Nat)
    {n : Nat} (names : Fin n → Nat) (distinct : Function.Injective names) :
    Coherent model source name names := by
  intro i j same a b one two
  have eq := distinct same
  subst j
  exact nominal_observation_unique model (.argument (.source source) name i.val) a b one two

/-- A syntactic point-bound sharing certificate suffices for semantic
coherence; it does not require pairwise observational equality as a premise. -/
theorem coherent_of_point_aliases (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models state model)
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor) {n : Nat} (names : Fin n → Nat)
    (bounds : Fin n → GeneralNominalInspection.Bounds state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (point : ∀ i, (bounds i).1 = (bounds i).2)
    (aliases : ∀ i j, names i = names j →
      state.base.source (bounds i).1 = state.base.source (bounds j).1) :
    Coherent model (state.base.source slot) descriptor.declaration.name names := by
  intro i j same a b one two
  have left := nominal_argument_bounds state model models slot descriptor recorded i.val (bounds i)
    (by rw [parameters]; simp [i.isLt])
  have right := nominal_argument_bounds state model models slot descriptor recorded j.val (bounds j)
    (by rw [parameters]; simp [j.isLt])
  have x := left.2 a one
  have y := right.2 b two
  rw [← point i] at x
  rw [← point j,← aliases i j same] at y
  exact ⟨subtype_trans x.2 y.1,subtype_trans y.2 x.1⟩

theorem projection_of_coherent (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models state model)
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor) {n : Nat} (names : Fin n → Nat)
    (bounds : Fin n → GeneralNominalInspection.Bounds state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (coherent : Coherent model (state.base.source slot) descriptor.declaration.name names) :
    ProjectionModels state (captured state slot descriptor.declaration.name names bounds) model := by
  have arg (i : Fin n) := nominal_argument_bounds state model models slot descriptor recorded i.val (bounds i)
    (by rw [parameters]; simp [i.isLt])
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
    simpa only [Nat.zero_add,Fits] using arg i
  · intro test member; cases member
  · intro a ha b hb same ref origin actual seen
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    cases Option.some.inj origin
    obtain ⟨other,observed⟩ := (arg j).1
    have fits := (arg j).2 other observed
    have eq := coherent i j same actual other (by simpa only [Nat.zero_add] using seen) observed
    exact ⟨subtype_trans fits.1 eq.2,subtype_trans eq.1 fits.2⟩
  · intro a ha b hb same x y hx hy u v hu hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    cases Option.some.inj hx; cases Option.some.inj hy
    exact coherent i j same u v (by simpa only [Nat.zero_add,embed] using hu)
      (by simpa only [Nat.zero_add,embed] using hv)

theorem coherent_of_projection (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (slot : Fin state.base.slots)
    (name : Nat) {n : Nat} (names : Fin n → Nat)
    (bounds : Fin n → GeneralNominalInspection.Bounds state)
    (projection : ProjectionModels state (captured state slot name names bounds) model) :
    Coherent model (state.base.source slot) name names := by
  intro i j same a b one two
  exact projection.2.2.2 _ (List.mem_ofFn.mpr ⟨i,rfl⟩) _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
    same _ _ rfl rfl a b (by simpa only [Nat.zero_add,embed] using one)
    (by simpa only [Nat.zero_add,embed] using two)

theorem compatible_of_coherent (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models state model)
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor) {n : Nat} (names : Fin n → Nat)
    (bounds : Fin n → GeneralNominalInspection.Bounds state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (coherent : Coherent model (state.base.source slot) descriptor.declaration.name names) :
    GeneralNominalAllocation.Compatible
      (bindings state (captured state slot descriptor.declaration.name names bounds)) model := by
  have arg (i : Fin n) := nominal_argument_bounds state model models slot descriptor recorded i.val (bounds i)
    (by rw [parameters]; simp [i.isLt])
  intro a ha b hb same
  simp only [bindings,captured,variablesReport,List.map_ofFn,Function.comp_def] at ha hb
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
  obtain ⟨x,hx⟩ := (arg i).1
  obtain ⟨y,hy⟩ := (arg j).1
  exact subtype_trans ((arg i).2 x hx).1
    (subtype_trans (coherent i j same x y hx hy).1 ((arg j).2 y hy).2)

theorem private_models_of_merges (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor) {n : Nat} (names : Fin n → Nat)
    (bounds : Fin n → GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models context.state model)
    (coherent : Coherent model (context.state.base.source slot) descriptor.declaration.name names)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges context.state registry root.identity declaration
        (bindings context.state (report context declaration [(slot,slot)])))) :
    GeneralNominalState.Models (privateState registry context root declaration [(slot,slot)]) model := by
  have calculated := report_exact context declaration slot descriptor recorded names bounds parameters query
  have arg (i : Fin n) := nominal_argument_bounds context.state model models slot descriptor recorded i.val (bounds i)
    (by rw [parameters]; simp [i.isLt])
  unfold privateState
  rw [calculated] at merges ⊢
  apply (GeneralNominalState.extend_models ..).mpr
  refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨models,?_,merges⟩,?_⟩
  · exact compatible_of_coherent context.state model models slot descriptor recorded names bounds parameters coherent
  · apply self_models
    intro i
    obtain ⟨actual,observed⟩ := (arg i).1
    exact subtype_trans ((arg i).2 actual observed).1 ((arg i).2 actual observed).2

/-- Exact decomposition with arbitrary finite repetition, including zero
positions. No distinctness or point-valued-interval assumption is hidden. -/
theorem branch_models_iff_residual (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor) {n : Nat} (names : Fin n → Nat)
    (bounds : Fin n → GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (model : GeneralNominalCommonBridge.Assignment) :
    BranchModels registry context root declaration checked [(slot,slot)] model ↔
      GeneralNominalState.Models context.state model ∧
      Coherent model (context.state.base.source slot) descriptor.declaration.name names ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalAllocation.merges context.state registry root.identity declaration
          (bindings context.state (report context declaration [(slot,slot)]))) ∧
      GeneralNominalMaterialization.Models context.state declaration
        (GeneralNominalAllocation.capture context.state registry root.identity declaration.id
          (bindings context.state (report context declaration [(slot,slot)])))
        (report context declaration [(slot,slot)])
        (generated registry context root declaration checked [(slot,slot)]) model := by
  have calculated := report_exact context declaration slot descriptor recorded names bounds parameters query
  constructor
  · intro branch
    have original := (branch_interval_sound registry context root declaration checked [(slot,slot)] model branch).1
    have projection := branch.2.1
    rw [calculated] at projection
    have propagated := ((GeneralNominalState.extend_models ..).mp branch.1).1
    exact ⟨original,coherent_of_projection context.state model slot descriptor.declaration.name names bounds projection,
      ((GeneralNominalAllocation.propagate_models ..).mp propagated).2.2,branch.2.2⟩
  · rintro ⟨original,coherent,merges,materialized⟩
    refine ⟨private_models_of_merges context registry root declaration slot descriptor recorded names bounds parameters query model original coherent merges,?_,materialized⟩
    rw [calculated]
    exact projection_of_coherent context.state model original slot descriptor recorded names bounds parameters coherent
end Yulang.GeneralNominalSharedCaptureFacts
