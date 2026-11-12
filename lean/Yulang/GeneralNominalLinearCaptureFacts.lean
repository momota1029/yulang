import Yulang.GeneralNominalBinaryCaptureFacts

/-! Arbitrary finite, distinct input binders under a nominal head. -/
namespace Yulang.GeneralNominalLinearCaptureFacts
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDeclarations CommonNominalFullCarrier

def variablesReport (state : GeneralNominalState.State) {n : Nat}
    (names : Fin n → Nat) (bounds : Fin n → GeneralNominalInspection.Bounds state)
    (origins : Nat → Origin) (offset : Nat) : Report state where
  captures := List.ofFn fun i => ⟨names i,bounds i,some (origins (offset+i.val))⟩
  checked := List.ofFn bounds
  anchors := List.ofFn fun i => (origins (offset+i.val),bounds i)

theorem inspectMany_exact (state : GeneralNominalState.State) {n : Nat}
    (names : Fin n → Nat) (bounds : Fin n → GeneralNominalInspection.Bounds state)
    (origins : Nat → Origin) (offset : Nat) :
    inspectMany state (List.ofFn fun i => .variables [names i]) (List.ofFn bounds)
      (fun i => some (origins i)) offset = variablesReport state names bounds origins offset := by
  induction n generalizing offset with
  | zero => simp [List.ofFn_zero,inspectMany,variablesReport]
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    simp only [inspectMany,inspect]
    rw [ih]
    simp [variablesReport,List.ofFn_succ,Report.append,Nat.add_comm,Nat.add_left_comm]

def captured (state : GeneralNominalState.State) (slot : Fin state.base.slots)
    (name : Nat) {n : Nat} (names : Fin n → Nat)
    (bounds : Fin n → GeneralNominalInspection.Bounds state) : Report state :=
  { variablesReport state names bounds
      (fun i => .nominal (.source (state.base.source slot)) name i) 0 with
    inspected := [(slot,slot)]
    checked := (slot,slot) :: (slot,slot) :: List.ofFn bounds }

theorem typeArguments_exact {slots n : Nat} (bounds : Fin n → (Fin slots × Fin slots)) :
    typeArguments (List.ofFn fun i => .type (bounds i)) = some (List.ofFn bounds) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have tail := ih (fun i => bounds i.succ)
    unfold typeArguments at tail ⊢
    simp only [List.ofFn_succ,List.mapM_cons]
    rw [tail]
    rfl

theorem report_exact (context : Context) (declaration : Declaration)
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor) {n : Nat}
    (names : Fin n → Nat) (bounds : Fin n → GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])]) :
    report context declaration [(slot,slot)] = captured context.state slot descriptor.declaration.name names bounds := by
  unfold report
  rw [query]
  simp only [inspectMany,inspect,recorded,parameters,typeArguments_exact,↓reduceIte]
  rw [inspectMany_exact]
  simp [captured,variablesReport,Report.visit,Report.append]

theorem projection_models (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (models : GeneralNominalState.Models state model) (slot : Fin state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.base.slots) (recorded : state.nominals slot = some descriptor)
    {n : Nat} (names : Fin n → Nat) (distinct : Function.Injective names)
    (bounds : Fin n → GeneralNominalInspection.Bounds state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i)) :
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
    have eq := distinct same
    subst j
    cases Option.some.inj origin
    exact (arg i).2 actual (by simpa only [Nat.zero_add] using seen)
  · intro a ha b hb same x y hx hy u v hu hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    have eq := distinct same
    subst j
    cases Option.some.inj hx; cases Option.some.inj hy
    exact nominal_observation_unique model
      (.argument (.source (state.base.source slot)) descriptor.declaration.name i.val) u v (by simpa only [Nat.zero_add,embed] using hu) (by simpa only [Nat.zero_add,embed] using hv)

/-- A distinct binder has exactly one captured interval, hence generates no
fresh lower-union/upper-intersection equations. -/
theorem filter_binding {α : Type} {n : Nat} (names : Fin n → Nat)
    (distinct : Function.Injective names) (values : Fin n → α) (i : Fin n) :
    (List.ofFn fun j => (names j,values j)).filter (fun x => x.1 == names i) =
      [(names i,values i)] := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [List.ofFn_succ,List.filter_cons]
      simp only [beq_self_eq_true,↓reduceIte]
      have empty : (List.ofFn fun j : Fin n => (names j.succ,values j.succ)).filter
          (fun x => x.1 == names 0) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro a member same
        obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
        have eq := distinct (of_decide_eq_true same)
        exact Fin.succ_ne_zero j eq
      rw [empty]
    · rw [List.ofFn_succ,List.filter_cons]
      have different : names 0 ≠ names k.succ := fun same =>
        Fin.succ_ne_zero k (distinct same).symm
      simp only [beq_eq_false_iff_ne.mpr different, Bool.false_eq_true, ↓reduceIte]
      exact ih (fun j => names j.succ) (fun _ _ same => Fin.succ_inj.mp (distinct same))
        (fun j => values j.succ) k

theorem occurrences_exact (state : GeneralNominalState.State) {n : Nat}
    (names : Fin n → Nat) (distinct : Function.Injective names)
    (bounds : Fin n → GeneralNominalInspection.Bounds state) (i : Fin n) :
    GeneralNominalAllocation.occurrences
      (List.ofFn fun j => (names j,state.base.source (bounds j).1,state.base.source (bounds j).2)) (names i) =
      [(state.base.source (bounds i).1,state.base.source (bounds i).2)] := by
  unfold GeneralNominalAllocation.occurrences
  rw [filter_binding names distinct]
  rfl

theorem propagated_models (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) {n : Nat} (names : Fin n → Nat) (distinct : Function.Injective names)
    (inputs : declaration.inputNames = List.ofFn names)
    (bounds : Fin n → GeneralNominalInspection.Bounds state)
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models state model)
    (valid : ∀ i, Subtype (model (state.base.source (bounds i).1)).1 (model (state.base.source (bounds i).2)).1) :
    GeneralNominalState.Models (GeneralNominalAllocation.propagate state registry invocation declaration
      (List.ofFn fun i => (names i,state.base.source (bounds i).1,state.base.source (bounds i).2))) model := by
  apply (GeneralNominalAllocation.propagate_models ..).mpr
  refine ⟨models,?_,?_⟩
  · intro a ha b hb same
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    have eq := distinct same
    subst j
    exact valid i
  · have empty : GeneralNominalAllocation.merges state registry invocation declaration
        (List.ofFn fun i => (names i,state.base.source (bounds i).1,state.base.source (bounds i).2)) = [] := by
      unfold GeneralNominalAllocation.merges
      rw [inputs]
      apply List.flatMap_eq_nil_iff.mpr
      intro name member
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
      rw [occurrences_exact state names distinct bounds i]
    rw [empty]
    intro atom member
    cases member

theorem self_models (state : GeneralNominalState.State) (slot : Fin state.base.slots)
    (name : Nat) {n : Nat} (names : Fin n → Nat) (bounds : Fin n → GeneralNominalInspection.Bounds state)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : ∀ i, Subtype (model (state.base.source (bounds i).1)).1 (model (state.base.source (bounds i).2)).1) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (selfChecks state (captured state slot name names bounds)) := by
  intro atom member
  obtain ⟨pair,present,rfl⟩ := List.mem_map.mp member
  simp only [captured,List.mem_cons] at present
  rcases present with rfl | rfl | present
  · exact subtype_refl _
  · exact subtype_refl _
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp present
    exact valid i

theorem private_models (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor) {n : Nat}
    (names : Fin n → Nat) (distinct : Function.Injective names)
    (inputs : declaration.inputNames = List.ofFn names)
    (bounds : Fin n → GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models context.state model) :
    GeneralNominalState.Models (privateState registry context root declaration [(slot,slot)]) model ∧
      ProjectionModels context.state (report context declaration [(slot,slot)]) model := by
  have calculated := report_exact context declaration slot descriptor recorded names bounds parameters query
  have valid (i : Fin n) : Subtype (model (context.state.base.source (bounds i).1)).1
      (model (context.state.base.source (bounds i).2)).1 := by
    have arg := nominal_argument_bounds context.state model models slot descriptor recorded i.val (bounds i)
      (by rw [parameters]; simp [i.isLt])
    obtain ⟨actual,seen⟩ := arg.1
    have fit := arg.2 actual seen
    exact subtype_trans fit.1 fit.2
  constructor
  · unfold privateState
    rw [calculated]
    apply (GeneralNominalState.extend_models ..).mpr
    constructor
    · simpa only [bindings,captured,variablesReport,List.map_ofFn,Function.comp_def] using
        propagated_models context.state registry root.identity declaration names distinct inputs bounds model models valid
    · exact self_models context.state slot descriptor.declaration.name names bounds model valid
  · rw [calculated]
    exact projection_models context.state model models slot descriptor recorded names distinct bounds parameters

/-- Exact remaining branch obligation for this syntax fragment: private
allocation and inspection are discharged; generated requests are not assumed
true merely from current-state consistency. -/
theorem branch_models_iff_materialized (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor) {n : Nat}
    (names : Fin n → Nat) (distinct : Function.Injective names)
    (inputs : declaration.inputNames = List.ofFn names)
    (bounds : Fin n → GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (model : GeneralNominalCommonBridge.Assignment) :
    BranchModels registry context root declaration checked [(slot,slot)] model ↔
      GeneralNominalState.Models context.state model ∧
      GeneralNominalMaterialization.Models context.state declaration
        (GeneralNominalAllocation.capture context.state registry root.identity declaration.id
          (bindings context.state (report context declaration [(slot,slot)])))
        (report context declaration [(slot,slot)])
        (generated registry context root declaration checked [(slot,slot)]) model := by
  constructor
  · intro branch
    exact ⟨(branch_interval_sound registry context root declaration checked [(slot,slot)] model branch).1,branch.2.2⟩
  · rintro ⟨original,materialized⟩
    have head := private_models context registry root declaration slot descriptor recorded
      names distinct inputs bounds parameters query model original
    exact ⟨head.1,head.2,materialized⟩

theorem report_finished (context : Context) (declaration : Declaration)
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor) {n : Nat}
    (names : Fin n → Nat) (bounds : Fin n → GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])]) :
    Finished (report context declaration [(slot,slot)]) := by
  rw [report_exact context declaration slot descriptor recorded names bounds parameters query]
  exact ⟨rfl,rfl,rfl⟩
end Yulang.GeneralNominalLinearCaptureFacts
