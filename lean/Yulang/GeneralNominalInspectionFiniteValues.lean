import Yulang.GeneralNominalFiniteBracket

/-! Scalar and invariant nominal inspection preserve finite input values.
Descriptor intervals retain their actual argument values without selecting
any interior point of an interval. -/
namespace Yulang.GeneralNominalInspectionFiniteValues
open GeneralNominalInspection (Bounds)
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalReadbackFunctionality GeneralNominalFiniteBracket GeneralNominalFiniteHeadInversion
open CommonNominalFullCarrier

theorem nominal_finite (term : Expr Nat) (closed : term.leaves = [])
    (below : Subtype (nominal name arguments) (denote (fun _ => .bottom) term)) :
    ∃ children : Fin arguments.length → Expr Nat,
      term = .node (.nominal name arguments.length) children ∧
      Equivalent (nominal name arguments) (denote (fun _ => .bottom) term) := by
  cases term with
  | leaf => simp [Expr.leaves] at closed
  | node test children =>
    let env : CommonNominalFullDemand.Environment Row := ⟨fun _ => .bottom,fun _ => [head test]⟩
    have accepted := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0 env (.role 0)
      ((build_role test _ env).mpr (List.mem_singleton_self _))
    have same : CommonNominalFullDemand.Head.nominal name arguments.length = head test := by
      rw [observe_nominal] at accepted
      change CommonNominalFullDemand.Head.nominal name (arguments.map (argumentAt 0)).length ∈ [head test] at accepted
      simpa only [List.length_map,List.mem_singleton] using accepted
    cases test with
    | scalar => cases same
    | structural shape => cases shape <;> cases same
    | nominal other count =>
      obtain ⟨rfl,rfl⟩ := CommonNominalFullDemand.Head.nominal.inj same
      exact ⟨children,rfl,below,(GeneralNominalIntervalLaws.nominal_subtype_equivalent _ _ _ _ below).2⟩

theorem scalar_finite (term : Expr Nat) (closed : term.leaves = [])
    (below : Subtype (.base base) (denote (fun _ => .bottom) term)) :
    ∃ children, term = .node (.scalar base) children := by
  cases term with
  | leaf => simp [Expr.leaves] at closed
  | node test children =>
    have same := subtype_head (.scalar base) test Fin.elim0 (fun i => denote (fun _ => .bottom) (children i)) below
    cases test with
    | scalar other => cases CommonNominalFullDemand.Head.base.inj same; exact ⟨children,rfl⟩
    | nominal => cases same
    | structural shape => cases shape <;> cases same

theorem scalar_slot (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) (slot : Fin state.base.slots)
    (recorded : state.view.heads slot = .scalar base) :
    Equivalent (model (state.base.source slot)).1 (.base base) :=
  GeneralNominalState.normalized_models state model valid slot (.base base) (by rw [recorded]; rfl)

theorem type_arguments (parameters : List (GeneralNominalState.Parameter slots))
    (found : typeArguments parameters = some intervals) : parameters = intervals.map GeneralNominalState.Parameter.type := by
  induction parameters generalizing intervals with
  | nil => cases Option.some.inj found; rfl
  | cons parameter rest ih =>
    cases parameter with
    | row => simp [typeArguments,List.mapM_cons] at found
    | type bounds =>
      simp only [typeArguments,List.mapM_cons] at found
      cases restFound : typeArguments rest with
      | none => simp only [typeArguments] at restFound; rw [restFound] at found; cases found
      | some tail =>
        have equation := restFound
        simp only [typeArguments] at restFound
        rw [restFound] at found
        cases Option.some.inj found
        simp only [List.map_cons]
        rw [ih equation]

theorem fits_types_length {state : GeneralSourceState.State} {model : GeneralNominalCommonBridge.Assignment}
    {intervals : List (Fin state.slots × Fin state.slots)} (fits : GeneralNominalState.FitsAll state model (intervals.map GeneralNominalState.Parameter.type) values) :
    intervals.length = values.length := by
  have all (parameters : List (GeneralNominalState.Parameter state.slots)) (values : List Argument)
      (fits : GeneralNominalState.FitsAll state model parameters values) : parameters.length = values.length := by
    induction fits with
    | nil => rfl
    | cons _ _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih
  simpa only [List.length_map] using all _ _ fits

theorem descriptor_finite (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) (slot : Fin state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.base.slots) (recorded : state.nominals slot = some descriptor)
    {intervals : List (Bounds state)}
    (found : typeArguments descriptor.arguments = some intervals)
    (term : Expr Nat) (closed : term.leaves = [])
    (below : Subtype (model (state.base.source slot)).1 (denote (fun _ => .bottom) term)) :
    ∃ children : Fin intervals.length → Expr Nat,
      term = .node (.nominal descriptor.declaration.name intervals.length) children ∧
      At model .actual (.source (state.base.source slot)) (denote (fun _ => .bottom) term) ∧
      ∀ index : Fin intervals.length, Fits state model intervals[index]
        (denote (fun _ => .bottom) (children index)) := by
  obtain ⟨values,fits,denoted⟩ := valid.2.1 slot descriptor recorded
  rw [type_arguments _ found] at fits
  have length := fits_types_length fits
  have finite := nominal_finite term closed (subtype_trans denoted.2 below)
  rw [← length] at finite
  obtain ⟨children,equal,same⟩ := finite
  refine ⟨children,equal,⟨⟨_,.source _⟩,?_⟩,?_⟩
  · intro actual seen; cases seen
    exact ⟨subtype_trans denoted.1 same.1,subtype_trans same.2 denoted.2⟩
  · intro index
    obtain ⟨value,located,contained⟩ := GeneralNominalIntervalLaws.fitsAll_at state.base model _ values fits index.val
      (.type intervals[index]) (by simp)
    have invariant := (nominal_regular_invariant_exact ..).mp (show Subtype (nominal descriptor.declaration.name values)
      (nominal descriptor.declaration.name (List.ofFn fun i => .inl (denote (fun _ => .bottom) (children i)))) by
        simpa only [equal,denote,build,arity] using same.1)
    have entry := invariant.2.2 index.val value (.inl (denote (fun _ => .bottom) (children index))) located (by simp [index.isLt])
    have fitted := (GeneralNominalIntervalLaws.fits_equivalent state.base model (.type intervals[index]) _ _ entry).mp contained
    exact fitted

end Yulang.GeneralNominalInspectionFiniteValues
