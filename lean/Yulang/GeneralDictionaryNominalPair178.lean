import Yulang.GeneralNominalSharedCaptureFacts
import Yulang.GeneralNominalIntervalLaws
import Yulang.GeneralDictionaryLinearLeaf

/-! Nonpoint nominal endpoints. Fresh capture equations stay explicit. -/
namespace Yulang.GeneralDictionaryNominalPair178
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralNominalLinearCaptureFacts GeneralDeclarations CommonNominalFullCarrier

 theorem observations_equivalent (model : GeneralNominalCommonBridge.Assignment)
    (lower upper name index : Nat)
    (below : Subtype (model lower).1 (model upper).1)
    (a b : Ty)
    (one : Observes model (.nominal (.source lower) name index) a)
    (two : Observes model (.nominal (.source upper) name index) b) : Equivalent a b := by
  cases one with
  | nominal parent left found =>
    cases parent
    cases two with
    | nominal parent right present =>
      cases parent
      have invariant := (nominal_regular_invariant_exact _ _ _ _).mp
        (subtype_trans left.2 (subtype_trans below right.1))
      exact invariant.2.2 index (.inl a) (.inl b) found present

 def pairReport (state : GeneralNominalState.State) (lower upper : Fin state.base.slots)
    (name : Nat) {n : Nat} (names : Fin n → Nat)
    (low high : Fin n → GeneralNominalInspection.Bounds state) : Report state :=
  { (variablesReport state names low (fun i => .nominal (.source (state.base.source lower)) name i) 0).append
    (variablesReport state names high (fun i => .nominal (.source (state.base.source upper)) name i) 0) with
    inspected := [(lower,upper)]
    checked := (lower,upper) :: (lower,upper) :: List.ofFn low ++ List.ofFn high }

 theorem report_exact (context : Context) (declaration : Declaration)
    (lower upper : Fin context.state.base.slots) (different : lower ≠ upper)
    (left right : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals lower = some left)
    (recordedRight : context.state.nominals upper = some right)
    (same : right.declaration.name = left.declaration.name)
    {n : Nat} (names : Fin n → Nat)
    (low high : Fin n → GeneralNominalInspection.Bounds context.state)
    (parameters : left.arguments = List.ofFn fun i => .type (low i))
    (parametersRight : right.arguments = List.ofFn fun i => .type (high i))
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal left.declaration.name (List.ofFn fun i => .variables [names i])]) :
    report context declaration [(lower,upper)] = pairReport context.state lower upper left.declaration.name names low high := by
  unfold report
  rw [query]
  simp only [inspectMany,inspect,recorded,recordedRight,parameters,parametersRight,
    typeArguments_exact,different,same,↓reduceIte]
  rw [inspectMany_exact,inspectMany_exact]
  simp [pairReport,variablesReport,Report.visit,Report.append]

 theorem projection_models (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models state model)
    (lower upper : Fin state.base.slots)
    (left right : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals lower = some left) (recordedRight : state.nominals upper = some right)
    (same : right.declaration.name = left.declaration.name)
    {n : Nat} (names : Fin n → Nat) (distinct : Function.Injective names)
    (low high : Fin n → GeneralNominalInspection.Bounds state)
    (parameters : left.arguments = List.ofFn fun i => .type (low i))
    (parametersRight : right.arguments = List.ofFn fun i => .type (high i))
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
      have ij := distinct eq
      subst j
      cases Option.some.inj origin
      simp only [Nat.zero_add] at seen
    · exact (lo i).2 actual seen
    · obtain ⟨other,observed⟩ := (hi i).1
      have fits := (hi i).2 other observed
      have e := cross i actual other seen observed
      exact ⟨subtype_trans fits.1 e.2,subtype_trans e.1 fits.2⟩
    · obtain ⟨other,observed⟩ := (lo i).1
      have fits := (lo i).2 other observed
      have e := cross i other actual observed seen
      exact ⟨subtype_trans fits.1 e.1,subtype_trans e.2 fits.2⟩
    · exact (hi i).2 actual seen
  · intro a ha b hb eq x y hx hy u v hu hv
    rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
    all_goals
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
      have ij := distinct eq
      subst j
      cases Option.some.inj hx; cases Option.some.inj hy
      simp only [Nat.zero_add] at hu hv
    · exact nominal_observation_unique model (.argument (.source (state.base.source lower)) left.declaration.name i.val) u v hu hv
    · exact cross i u v hu hv
    · have e := cross i v u hv hu; exact ⟨e.2,e.1⟩
    · exact nominal_observation_unique model (.argument (.source (state.base.source upper)) left.declaration.name i.val) u v hu hv

/-- Distinct outer slots, but parameter intervals need not be point intervals. -/
structure Shape (context : Context) (declaration : Declaration) where
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
  distinct : Function.Injective names
  low : Fin n → GeneralNominalInspection.Bounds context.state
  high : Fin n → GeneralNominalInspection.Bounds context.state
  parameters : left.arguments = List.ofFn fun i => .type (low i)
  parametersRight : right.arguments = List.ofFn fun i => .type (high i)
  query : GeneralNominalInspection.queries context.state context.interpretation declaration =
    [.nominal left.declaration.name (List.ofFn fun i => .variables [names i])]

 theorem compatible_of_projection (state : GeneralNominalState.State)
    (lower upper : Fin state.base.slots) (name : Nat) {n : Nat}
    (names : Fin n → Nat) (low high : Fin n → GeneralNominalInspection.Bounds state)
    (model : GeneralNominalCommonBridge.Assignment)
    (projection : ProjectionModels state (pairReport state lower upper name names low high) model) :
    GeneralNominalAllocation.Compatible (bindings state (pairReport state lower upper name names low high)) model := by
  intro first one last two same
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp one
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp two
  have anchored : ∃ ref, a.origin = some ref ∧ (ref,a.bounds) ∈
      (pairReport state lower upper name names low high).anchors := by
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      exact ⟨_,rfl,List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)⟩
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      exact ⟨_,rfl,List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩)⟩
  obtain ⟨ref,origin,anchor⟩ := anchored
  obtain ⟨actual,seen⟩ := (projection.1 _ anchor).1
  exact subtype_trans ((projection.1 _ anchor).2 actual seen).1
    (projection.2.2.1 a ha b hb same ref origin actual seen).2

 theorem self_models (state : GeneralNominalState.State)
    (lower upper : Fin state.base.slots) (name : Nat) {n : Nat}
    (names : Fin n → Nat) (low high : Fin n → GeneralNominalInspection.Bounds state)
    (model : GeneralNominalCommonBridge.Assignment)
    (below : Subtype (model (state.base.source lower)).1 (model (state.base.source upper)).1)
    (projection : ProjectionModels state (pairReport state lower upper name names low high) model) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (selfChecks state (pairReport state lower upper name names low high)) := by
  intro atom member
  obtain ⟨pair,present,rfl⟩ := List.mem_map.mp member
  simp only [pairReport,List.mem_cons,List.mem_append] at present
  rcases present with (rfl | rfl | present) | present
  · exact below
  · exact below
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp present
    have anchor := projection.1 _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
    obtain ⟨actual,seen⟩ := anchor.1
    exact subtype_trans (anchor.2 actual seen).1 (anchor.2 actual seen).2
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp present
    have anchor := projection.1 _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
    obtain ⟨actual,seen⟩ := anchor.1
    exact subtype_trans (anchor.2 actual seen).1 (anchor.2 actual seen).2

 theorem private_models_of_merges (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (shape : Shape context declaration) (model : GeneralNominalCommonBridge.Assignment)
    (models : GeneralNominalState.Models context.state model)
    (below : Subtype (model (context.state.base.source shape.lower)).1
      (model (context.state.base.source shape.upper)).1)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges context.state registry root.identity declaration
        (bindings context.state (report context declaration [(shape.lower,shape.upper)])))) :
    GeneralNominalState.Models (privateState registry context root declaration [(shape.lower,shape.upper)]) model := by
  have calculated := report_exact context declaration shape.lower shape.upper shape.different shape.left shape.right
    shape.recorded shape.recordedRight shape.same shape.names shape.low shape.high shape.parameters shape.parametersRight shape.query
  have projection := projection_models context.state model models shape.lower shape.upper shape.left shape.right
    shape.recorded shape.recordedRight shape.same shape.names shape.distinct shape.low shape.high shape.parameters shape.parametersRight below
  unfold privateState
  rw [calculated] at merges ⊢
  apply (GeneralNominalState.extend_models ..).mpr
  exact ⟨(GeneralNominalAllocation.propagate_models ..).mpr
    ⟨models,compatible_of_projection _ _ _ _ _ _ _ _ projection,merges⟩,
    self_models _ _ _ _ _ _ _ _ below projection⟩

/-- The only residual condition for this terminal shape is truth of the actual
fresh capture-merge equations. These equations are not asserted automatically. -/
 theorem branch_models_iff_merges (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape context declaration) (terminal : declaration.requirements = [])
    (outputs : root.demand.outputs = []) (model : GeneralNominalCommonBridge.Assignment)
    (models : GeneralNominalState.Models context.state model)
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
    refine ⟨private_models_of_merges context registry root declaration shape model models below merges,?_,?_⟩
    · rw [report_exact context declaration shape.lower shape.upper shape.different shape.left shape.right
        shape.recorded shape.recordedRight shape.same shape.names shape.low shape.high shape.parameters shape.parametersRight shape.query]
      exact projection_models context.state model models shape.lower shape.upper shape.left shape.right
        shape.recorded shape.recordedRight shape.same shape.names shape.distinct shape.low shape.high shape.parameters shape.parametersRight below
    · rw [GeneralDictionaryLinearLeaf.generated_empty context registry root declaration checked terminal outputs]
      exact GeneralNominalMaterialization.empty_models ..

/-- Source validity and endpoint order are themselves recoverable from a branch;
all remaining branch conditions reduce to the explicit allocation equations. -/
 theorem branch_models_iff_residual (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape context declaration) (terminal : declaration.requirements = [])
    (outputs : root.demand.outputs = []) (model : GeneralNominalCommonBridge.Assignment) :
    BranchModels registry context root declaration checked [(shape.lower,shape.upper)] model ↔
    GeneralNominalState.Models context.state model ∧
    Subtype (model (context.state.base.source shape.lower)).1
      (model (context.state.base.source shape.upper)).1 ∧
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges context.state registry root.identity declaration
        (bindings context.state (report context declaration [(shape.lower,shape.upper)]))) := by
  constructor
  · intro branch
    have extended := (GeneralNominalState.extend_models ..).mp branch.1
    have propagated := (GeneralNominalAllocation.propagate_models ..).mp extended.1
    refine ⟨propagated.1,?_,propagated.2.2⟩
    exact extended.2 (.tyLe (.var (context.state.base.source shape.lower))
      (.var (context.state.base.source shape.upper)))
      (List.mem_map.mpr ⟨(shape.lower,shape.upper),by simp [report],rfl⟩)
  · rintro ⟨models,below,merges⟩
    exact (branch_models_iff_merges context registry root declaration checked shape terminal outputs model models below).mpr merges
end Yulang.GeneralDictionaryNominalPair178
