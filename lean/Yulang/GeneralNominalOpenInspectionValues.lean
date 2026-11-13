import Yulang.GeneralNominalOpenPatternLabels

/-! Actual interval inversion at explicit constructor nodes. Hole values are
arbitrary carrier types; no property of a hole is inferred from its name. -/
namespace Yulang.GeneralNominalOpenInspectionValues
open GeneralNominalInspection (Bounds)
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalReadbackFunctionality GeneralNominalFiniteBracket GeneralNominalFiniteHeadInversion
open GeneralNominalInspectionFiniteValues CommonNominalFullCarrier

theorem nominal_open (values : Nat → Ty) (term : Expr Nat) (explicit : ∀ name, term ≠ .leaf name)
    (below : Subtype (nominal name arguments) (denote values term)) :
    ∃ children : Fin arguments.length → Expr Nat,
      term = .node (.nominal name arguments.length) children ∧
      Equivalent (nominal name arguments) (denote values term) := by
  cases term with
  | leaf name => exact False.elim (explicit name rfl)
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

theorem scalar_open (values : Nat → Ty) (term : Expr Nat) (explicit : ∀ name, term ≠ .leaf name)
    (below : Subtype (.base base) (denote values term)) :
    ∃ children, term = .node (.scalar base) children := by
  cases term with
  | leaf name => exact False.elim (explicit name rfl)
  | node test children =>
    have same := subtype_head (.scalar base) test Fin.elim0 (fun i => denote values (children i)) below
    cases test with
    | scalar other => cases CommonNominalFullDemand.Head.base.inj same; exact ⟨children,rfl⟩
    | nominal => cases same
    | structural shape => cases shape <;> cases same

theorem descriptor_open (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) (slot : Fin state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.base.slots) (recorded : state.nominals slot = some descriptor)
    {intervals : List (Bounds state)}
    (found : typeArguments descriptor.arguments = some intervals)
    (values : Nat → Ty) (term : Expr Nat) (explicit : ∀ name, term ≠ .leaf name)
    (below : Subtype (model (state.base.source slot)).1 (denote values term)) :
    ∃ children : Fin intervals.length → Expr Nat,
      term = .node (.nominal descriptor.declaration.name intervals.length) children ∧
      At model .actual (.source (state.base.source slot)) (denote values term) ∧
      ∀ index : Fin intervals.length, Fits state model intervals[index]
        (denote values (children index)) := by
  obtain ⟨arguments,fits,denoted⟩ := valid.2.1 slot descriptor recorded
  rw [type_arguments _ found] at fits
  have length := fits_types_length fits
  have finite := nominal_open values term explicit (subtype_trans denoted.2 below)
  rw [← length] at finite
  obtain ⟨children,equal,same⟩ := finite
  refine ⟨children,equal,⟨⟨_,.source _⟩,?_⟩,?_⟩
  · intro actual seen; cases seen
    exact ⟨subtype_trans denoted.1 same.1,subtype_trans same.2 denoted.2⟩
  · intro index
    obtain ⟨value,located,contained⟩ := GeneralNominalIntervalLaws.fitsAll_at state.base model _ arguments fits index.val
      (.type intervals[index]) (by simp)
    have invariant := (nominal_regular_invariant_exact ..).mp (show Subtype (nominal descriptor.declaration.name arguments)
      (nominal descriptor.declaration.name (List.ofFn fun i => .inl (denote values (children i)))) by
        simpa only [equal,denote,build,arity] using same.1)
    have entry := invariant.2.2 index.val value (.inl (denote values (children index))) located (by simp [index.isLt])
    have fitted := (GeneralNominalIntervalLaws.fits_equivalent state.base model (.type intervals[index]) _ _ entry).mp contained
    exact fitted

theorem open_bracket (values : Nat → Ty) (term : Expr Nat) (explicit : ∀ name, term ≠ .leaf name) (canonical : Canonical term)
    (test : Test) (testCanonical : TestCanonical test) (lower upper : Fin (arity test) → Ty)
    (below : Subtype (build test lower) (denote values term))
    (above : Subtype (denote values term) (build test upper)) :
    ∃ children, term = .node test children := by
  cases term with
  | leaf name => exact False.elim (explicit name rfl)
  | node middle children =>
    have same := test_bracket test middle lower (fun index => denote values (children index)) upper
      testCanonical canonical.1 below above
    subst middle
    exact ⟨children,rfl⟩

theorem structural_open (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) (bounds : GeneralNominalInspection.Bounds state)
    (lowerKind upperKind : Fin state.view.kinds)
    (lower : Fin (state.view.shapes lowerKind).arity → Fin state.base.slots)
    (upper : Fin (state.view.shapes upperKind).arity → Fin state.base.slots)
    (lowerAt : state.view.heads bounds.1 = .structural lowerKind lower)
    (upperAt : state.view.heads bounds.2 = .structural upperKind upper)
    (lowerShape : state.view.shapes lowerKind = shape) (upperShape : state.view.shapes upperKind = shape)
    (values : Nat → Ty) (term : Expr Nat) (explicit : ∀ name, term ≠ .leaf name) (canonical : Canonical term)
    (contained : Fits state model bounds (denote values term)) :
    ∃ children : Fin shape.arity → Expr Nat, term = .node (.structural shape) children ∧
      ∀ index, Fits state model (reindex lowerShape lower index,reindex upperShape upper index)
        (denote values (children index)) := by
  have one := structural_slot state model valid bounds.1 lowerKind lower lowerAt lowerShape
  have two := structural_slot state model valid bounds.2 upperKind upper upperAt upperShape
  have below := subtype_trans one.2 contained.1
  have above := subtype_trans contained.2 two.1
  have shapeCanonical : shape.Canonical := lowerShape ▸ state.view.canonical lowerKind
  obtain ⟨children,equal⟩ := open_bracket values term explicit canonical (.structural shape) shapeCanonical _ _ below above
  refine ⟨children,equal,?_⟩
  rw [equal] at below above
  exact structural_children shape shapeCanonical _ _ _ below above


end Yulang.GeneralNominalOpenInspectionValues
