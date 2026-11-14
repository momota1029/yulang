import Yulang.GeneralDictionaryNominalPair178

/-! Arbitrary repeated binder names across finite nonpoint nominal arguments.
Projection coherence is exact and separate from fresh merge equations. -/
namespace Yulang.GeneralDictionaryNominalPairShared178
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralNominalLinearCaptureFacts GeneralDictionaryNominalPair178
open GeneralDeclarations CommonNominalFullCarrier
 theorem projection_of_coherent (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models state model)
    (lower upper : Fin state.base.slots)
    (left right : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals lower = some left) (recordedRight : state.nominals upper = some right)
    (same : right.declaration.name = left.declaration.name)
    {n : Nat} (names : Fin n → Nat)
    (low high : Fin n → GeneralNominalInspection.Bounds state)
    (parameters : left.arguments = List.ofFn fun i => .type (low i))
    (parametersRight : right.arguments = List.ofFn fun i => .type (high i))
    (coherent : GeneralNominalSharedCaptureFacts.Coherent model (state.base.source lower) left.declaration.name names)
    (below : Subtype (model (state.base.source lower)).1 (model (state.base.source upper)).1) :
    ProjectionModels state (pairReport state lower upper left.declaration.name names low high) model := by
  have lo (i : Fin n) := nominal_argument_bounds state model models lower left recorded i.val (low i)
    (by rw [parameters]; simp [i.isLt])
  have hi (i : Fin n) : (∃ actual, Observes model (.nominal (.source (state.base.source upper)) left.declaration.name i.val) actual) ∧
      ∀ actual, Observes model (.nominal (.source (state.base.source upper)) left.declaration.name i.val) actual →
        GeneralNominalCaptureMerges.Fits model (state.base.source (high i).1,state.base.source (high i).2) actual := by
    simpa only [same] using nominal_argument_bounds state model models upper right recordedRight i.val (high i)
      (by rw [parametersRight]; simp [i.isLt])
  have cross (i : Fin n) (a b : Ty)
      (ha : Observes model (.nominal (.source (state.base.source lower)) left.declaration.name i.val) a)
      (hb : Observes model (.nominal (.source (state.base.source upper)) left.declaration.name i.val) b) : Equivalent a b :=
    observations_equivalent model _ _ _ _ below a b ha hb
  have lh (i j : Fin n) (eq : names i = names j) (a b : Ty)
      (ha : Observes model (.nominal (.source (state.base.source lower)) left.declaration.name i.val) a)
      (hb : Observes model (.nominal (.source (state.base.source upper)) left.declaration.name j.val) b) : Equivalent a b := by
    obtain ⟨v,hv⟩ := (lo j).1
    have one := coherent i j eq a v ha hv
    have two := cross j v b hv hb
    exact ⟨subtype_trans one.1 two.1,subtype_trans two.2 one.2⟩
  have hl (i j : Fin n) (eq : names i = names j) (a b : Ty)
      (ha : Observes model (.nominal (.source (state.base.source upper)) left.declaration.name i.val) a)
      (hb : Observes model (.nominal (.source (state.base.source lower)) left.declaration.name j.val) b) : Equivalent a b := by
    have e := lh j i eq.symm b a hb ha
    exact ⟨e.2,e.1⟩
  have hh (i j : Fin n) (eq : names i = names j) (a b : Ty)
      (ha : Observes model (.nominal (.source (state.base.source upper)) left.declaration.name i.val) a)
      (hb : Observes model (.nominal (.source (state.base.source upper)) left.declaration.name j.val) b) : Equivalent a b := by
    obtain ⟨v,hv⟩ := (lo i).1
    have one := cross i v a hv ha
    have two := lh i j eq v b hv hb
    exact ⟨subtype_trans one.2 two.1,subtype_trans two.2 one.1⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
      simpa only [Nat.zero_add,Fits] using lo i
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
      simpa only [Nat.zero_add,Fits] using hi i
  · intro test member; cases member
  · intro a ha b hb eq ref origin actual seen
    rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
    all_goals
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
      cases Option.some.inj origin
      simp only [Nat.zero_add] at seen
    · obtain ⟨other,observed⟩ := (lo j).1
      have fits := (lo j).2 other observed
      have e := coherent i j eq actual other seen observed
      exact ⟨subtype_trans fits.1 e.2,subtype_trans e.1 fits.2⟩
    · obtain ⟨other,observed⟩ := (hi j).1
      have fits := (hi j).2 other observed
      have e := lh i j eq actual other seen observed
      exact ⟨subtype_trans fits.1 e.2,subtype_trans e.1 fits.2⟩
    · obtain ⟨other,observed⟩ := (lo j).1
      have fits := (lo j).2 other observed
      have e := hl i j eq actual other seen observed
      exact ⟨subtype_trans fits.1 e.2,subtype_trans e.1 fits.2⟩
    · obtain ⟨other,observed⟩ := (hi j).1
      have fits := (hi j).2 other observed
      have e := hh i j eq actual other seen observed
      exact ⟨subtype_trans fits.1 e.2,subtype_trans e.1 fits.2⟩
  · intro a ha b hb eq x y hx hy u v hu hv
    rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
    all_goals
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
      cases Option.some.inj hx; cases Option.some.inj hy
      simp only [Nat.zero_add] at hu hv
    · exact coherent i j eq u v hu hv
    · exact lh i j eq u v hu hv
    · exact hl i j eq u v hu hv
    · exact hh i j eq u v hu hv

theorem coherent_of_projection (state : GeneralNominalState.State)
    (lower upper : Fin state.base.slots) (name : Nat) {n : Nat} (names : Fin n → Nat)
    (low high : Fin n → GeneralNominalInspection.Bounds state)
    (model : GeneralNominalCommonBridge.Assignment)
    (projection : ProjectionModels state (pairReport state lower upper name names low high) model) :
    GeneralNominalSharedCaptureFacts.Coherent model (state.base.source lower) name names := by
  intro i j same a b one two
  exact projection.2.2.2 _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
    _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨j,rfl⟩)) same _ _ rfl rfl a b
    (by simpa only [Nat.zero_add,embed] using one) (by simpa only [Nat.zero_add,embed] using two)

structure SharedShape (context : Context) (declaration : Declaration) where
  lower : Fin context.state.base.slots
  upper : Fin context.state.base.slots
  different : lower ≠ upper
  left : GeneralNominalState.Descriptor context.state.base.slots
  right : GeneralNominalState.Descriptor context.state.base.slots
  recorded : context.state.nominals lower = some left
  recordedRight : context.state.nominals upper = some right
  same : right.declaration.name = left.declaration.name
  n : Nat
  names : Fin n → Nat
  low : Fin n → GeneralNominalInspection.Bounds context.state
  high : Fin n → GeneralNominalInspection.Bounds context.state
  parameters : left.arguments = List.ofFn fun i => .type (low i)
  parametersRight : right.arguments = List.ofFn fun i => .type (high i)
  query : GeneralNominalInspection.queries context.state context.interpretation declaration =
    [.nominal left.declaration.name (List.ofFn fun i => .variables [names i])]

 theorem private_models_of_merges (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (shape : SharedShape context declaration) (model : GeneralNominalCommonBridge.Assignment)
    (models : GeneralNominalState.Models context.state model)
    (coherent : GeneralNominalSharedCaptureFacts.Coherent model (context.state.base.source shape.lower) shape.left.declaration.name shape.names)
    (below : Subtype (model (context.state.base.source shape.lower)).1
      (model (context.state.base.source shape.upper)).1)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges context.state registry root.identity declaration
        (bindings context.state (report context declaration [(shape.lower,shape.upper)])))) :
    GeneralNominalState.Models (privateState registry context root declaration [(shape.lower,shape.upper)]) model := by
  have calculated := report_exact context declaration shape.lower shape.upper shape.different shape.left shape.right
    shape.recorded shape.recordedRight shape.same shape.names shape.low shape.high shape.parameters shape.parametersRight shape.query
  have projection := projection_of_coherent context.state model models shape.lower shape.upper shape.left shape.right
    shape.recorded shape.recordedRight shape.same shape.names shape.low shape.high shape.parameters shape.parametersRight coherent below
  unfold privateState
  rw [calculated] at merges ⊢
  apply (GeneralNominalState.extend_models ..).mpr
  exact ⟨(GeneralNominalAllocation.propagate_models ..).mpr
    ⟨models,compatible_of_projection _ _ _ _ _ _ _ _ projection,merges⟩,
    self_models _ _ _ _ _ _ _ _ below projection⟩

/-- After source validity, endpoint order and shared-name coherence, the
remaining terminal condition is the actual fresh capture-merge equations. -/
 theorem branch_models_iff_merges (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : SharedShape context declaration) (terminal : declaration.requirements = [])
    (outputs : root.demand.outputs = []) (model : GeneralNominalCommonBridge.Assignment)
    (models : GeneralNominalState.Models context.state model)
    (coherent : GeneralNominalSharedCaptureFacts.Coherent model (context.state.base.source shape.lower) shape.left.declaration.name shape.names)
    (below : Subtype (model (context.state.base.source shape.lower)).1
      (model (context.state.base.source shape.upper)).1) :
    BranchModels registry context root declaration checked [(shape.lower,shape.upper)] model ↔
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges context.state registry root.identity declaration
        (bindings context.state (report context declaration [(shape.lower,shape.upper)]))) := by
  constructor
  · intro branch
    have propagated := ((GeneralNominalState.extend_models ..).mp branch.1).1
    exact ((GeneralNominalAllocation.propagate_models ..).mp propagated).2.2
  · intro merges
    refine ⟨private_models_of_merges context registry root declaration shape model models coherent below merges,?_,?_⟩
    · rw [report_exact context declaration shape.lower shape.upper shape.different shape.left shape.right
        shape.recorded shape.recordedRight shape.same shape.names shape.low shape.high shape.parameters shape.parametersRight shape.query]
      exact projection_of_coherent context.state model models shape.lower shape.upper shape.left shape.right
        shape.recorded shape.recordedRight shape.same shape.names shape.low shape.high shape.parameters shape.parametersRight coherent below
    · rw [GeneralDictionaryLinearLeaf.generated_empty context registry root declaration checked terminal outputs]
      exact GeneralNominalMaterialization.empty_models ..

/-- Exact repeated-name residual: semantic sharing at the lower nominal,
outer endpoint order, source validity, and actual merge equations. -/
theorem branch_models_iff_shared_residual (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : SharedShape context declaration) (terminal : declaration.requirements = [])
    (outputs : root.demand.outputs = []) (model : GeneralNominalCommonBridge.Assignment) :
    BranchModels registry context root declaration checked [(shape.lower,shape.upper)] model ↔
    GeneralNominalState.Models context.state model ∧
    Subtype (model (context.state.base.source shape.lower)).1
      (model (context.state.base.source shape.upper)).1 ∧
    GeneralNominalSharedCaptureFacts.Coherent model (context.state.base.source shape.lower)
      shape.left.declaration.name shape.names ∧
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges context.state registry root.identity declaration
        (bindings context.state (report context declaration [(shape.lower,shape.upper)]))) := by
  constructor
  · intro branch
    have extended := (GeneralNominalState.extend_models ..).mp branch.1
    have propagated := (GeneralNominalAllocation.propagate_models ..).mp extended.1
    refine ⟨propagated.1,?_,?_,propagated.2.2⟩
    · exact extended.2 (.tyLe (.var (context.state.base.source shape.lower))
        (.var (context.state.base.source shape.upper)))
        (List.mem_map.mpr ⟨(shape.lower,shape.upper),by simp [report],rfl⟩)
    · have projection := branch.2.1
      rw [report_exact context declaration shape.lower shape.upper shape.different shape.left shape.right
        shape.recorded shape.recordedRight shape.same shape.names shape.low shape.high shape.parameters shape.parametersRight shape.query] at projection
      exact coherent_of_projection _ _ _ _ _ _ _ _ projection
  · rintro ⟨models,below,coherent,merges⟩
    exact (branch_models_iff_merges context registry root declaration checked shape terminal outputs model models coherent below).mpr merges
end Yulang.GeneralDictionaryNominalPairShared178
