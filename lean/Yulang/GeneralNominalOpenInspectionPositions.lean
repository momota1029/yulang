import Yulang.GeneralNominalOpenInspectionValues

/-! Actual inspection positions over arbitrary hole valuations. Both the
interval and the retained actual origin refer to the same finite expression. -/
namespace Yulang.GeneralNominalOpenInspectionPositions
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds)
open GeneralNominalOriginTerms GeneralNominalFiniteMeaning GeneralNominalReadbackFunctionality
open GeneralNominalInspectionAlignment
open GeneralNominalInspectionPositions (zip_reindex)

def Input (values : Nat → CommonNominalFullCarrier.Ty) (model : GeneralNominalCommonBridge.Assignment)
    (state : GeneralNominalState.State) (bounds : Bounds state) (origin : Option Origin) (term : Expr Nat) : Prop :=
  Canonical term ∧ Fits state model bounds (denote values term) ∧
    ∀ root, origin = some root → At model .actual root (denote values term)

def InputsAt (values : Nat → CommonNominalFullCarrier.Ty) (model : GeneralNominalCommonBridge.Assignment)
    (state : GeneralNominalState.State) (origins : Nat → Option Origin) :
    Nat → List (Bounds state) → List (Expr Nat) → Prop
  | _,[],[] => True
  | offset,bounds :: intervals,term :: terms => Input values model state bounds (origins offset) term ∧
      InputsAt values model state origins (offset+1) intervals terms
  | _,_,_ => False

theorem inputs_at (bounds : List (Bounds state)) (terms : List (Expr Nat)) (length : terms.length = bounds.length)
    (known : ∀ index : Fin bounds.length, Input values model state bounds[index] (origins (offset+index.val))
      (terms[index.val]'(by rw [length]; exact index.isLt))) : InputsAt values model state origins offset bounds terms := by
  induction bounds generalizing terms offset with
  | nil => have empty : terms = [] := List.eq_nil_of_length_eq_zero length; subst terms; trivial
  | cons head tail ih =>
    cases terms with
    | nil => cases length
    | cons term rest =>
      refine ⟨by simpa using known ⟨0,by simp⟩,?_⟩
      apply ih rest (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using length)
      intro index
      have next := known ⟨index.val+1,by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using index.isLt⟩
      simpa [Nat.add_assoc,Nat.add_comm 1 index.val] using next

theorem retained_child (known : ∀ root, origin = some root → At model .actual root
      (denote values (.node test children)))
    (canonical : Canonical (.node test children)) (index : Fin (arity test)) :
    ∀ root, origin.map (fun parent => project parent test index) = some root →
      At model .actual root (denote values (children index)) := by
  intro root recorded
  obtain ⟨parent,present,equal⟩ := Option.map_eq_some_iff.mp recorded
  subst root
  exact project_value test canonical.1 _ (known parent present) index

theorem structural_inputs (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) (bounds : Bounds state)
    (lowerKind upperKind : Fin state.view.kinds)
    (lower : Fin (state.view.shapes lowerKind).arity → Fin state.base.slots)
    (upper : Fin (state.view.shapes upperKind).arity → Fin state.base.slots)
    (lowerAt : state.view.heads bounds.1 = .structural lowerKind lower)
    (upperAt : state.view.heads bounds.2 = .structural upperKind upper)
    (lowerShape : state.view.shapes lowerKind = shape) (upperShape : state.view.shapes upperKind = shape)
    (known : Input values model state bounds origin term) (explicit : ∀ name, term ≠ .leaf name) :
    ∃ children : Fin shape.arity → Expr Nat, term = .node (.structural shape) children ∧
      InputsAt values model state (fun index => origin.map fun parent => .structural parent shape index) 0
        ((List.ofFn lower).zip (List.ofFn upper)) (List.ofFn children) := by
  obtain ⟨canonical,contained,retained⟩ := known
  obtain ⟨children,equal,fits⟩ := GeneralNominalOpenInspectionValues.structural_open state model valid bounds
    lowerKind upperKind lower upper lowerAt upperAt lowerShape upperShape values term explicit canonical contained
  refine ⟨children,equal,?_⟩
  rw [equal] at canonical retained
  rw [zip_reindex lowerShape upperShape]
  apply inputs_at _ _ (by simp)
  intro index
  let position : Fin shape.arity := ⟨index.val,by simpa only [List.length_ofFn] using index.isLt⟩
  simp only [Fin.getElem_fin,List.getElem_ofFn,Nat.zero_add]
  refine ⟨canonical.2 position,fits position,?_⟩
  exact retained_child retained canonical position

theorem nominal_inputs (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) (bounds : Bounds state)
    (descriptor : GeneralNominalState.Descriptor state.base.slots) (recorded : state.nominals bounds.1 = some descriptor)
    {intervals : List (Bounds state)} (found : typeArguments descriptor.arguments = some intervals)
    (known : Input values model state bounds origin term) (explicit : ∀ name, term ≠ .leaf name) :
    ∃ children : Fin intervals.length → Expr Nat, term = .node (.nominal descriptor.declaration.name intervals.length) children ∧
      InputsAt values model state
        (fun index => some (.nominal (origin.getD (.source (state.base.source bounds.1))) descriptor.declaration.name index)) 0
        intervals (List.ofFn children) := by
  obtain ⟨canonical,contained,retained⟩ := known
  obtain ⟨children,equal,endpoint,fits⟩ := GeneralNominalOpenInspectionValues.descriptor_open state model valid bounds.1
    descriptor recorded found values term explicit contained.1
  refine ⟨children,equal,?_⟩
  rw [equal] at canonical retained endpoint
  have parent : At model .actual (origin.getD (.source (state.base.source bounds.1)))
      (denote values (.node (.nominal descriptor.declaration.name intervals.length) children)) := by
    cases origin with
    | none => exact endpoint
    | some root => exact retained root rfl
  apply inputs_at _ _ (List.length_ofFn ..)
  intro index
  simp only [Fin.getElem_fin,List.getElem_ofFn,Nat.zero_add]
  refine ⟨canonical.2 index,fits index,?_⟩
  intro root recorded
  cases Option.some.inj recorded
  exact project_value (.nominal descriptor.declaration.name intervals.length) trivial _ parent index


end Yulang.GeneralNominalOpenInspectionPositions
