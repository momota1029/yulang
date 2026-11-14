import Yulang.GeneralNominalNamedArgumentReadback

/-! Actual inspection input inversion with one finite syntax tree shared by
all models. Inversion chooses subtrees of that fixed tree, not new semantic
representatives separately in different models. -/
namespace Yulang.GeneralNominalUniformInspectionInputs
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds)
open GeneralNominalOriginTerms GeneralNominalFiniteMeaning GeneralNominalReadbackFunctionality

variable {models : GeneralNominalCommonBridge.Assignment → Prop}
variable {values : GeneralNominalCommonBridge.Assignment → Nat → CommonNominalFullCarrier.Ty}

def Input (models : GeneralNominalCommonBridge.Assignment → Prop)
    (values : GeneralNominalCommonBridge.Assignment → Nat → CommonNominalFullCarrier.Ty)
    (state : GeneralNominalState.State) (bounds : Bounds state) (origin : Option Origin) (term : Expr Nat) : Prop :=
  ∀ model, models model → GeneralNominalOpenInspectionPositions.Input (values model) model state bounds origin term

def InputsAt (models : GeneralNominalCommonBridge.Assignment → Prop)
    (values : GeneralNominalCommonBridge.Assignment → Nat → CommonNominalFullCarrier.Ty)
    (state : GeneralNominalState.State) (origins : Nat → Option Origin)
    (offset : Nat) (bounds : List (Bounds state)) (terms : List (Expr Nat)) : Prop :=
  ∀ model, models model → GeneralNominalOpenInspectionPositions.InputsAt (values model) model state origins offset bounds terms

theorem node_injective {first last : Fin (arity test) → Expr Nat}
    (equal : Expr.node test first = Expr.node test last) : first = last := by
  cases equal
  rfl

theorem structural_inputs (state : GeneralNominalState.State)
    (inhabited : ∃ model, models model)
    (valid : ∀ model, models model → GeneralNominalState.Models state model) (bounds : Bounds state)
    (lowerKind upperKind : Fin state.view.kinds)
    (lower : Fin (state.view.shapes lowerKind).arity → Fin state.base.slots)
    (upper : Fin (state.view.shapes upperKind).arity → Fin state.base.slots)
    (lowerAt : state.view.heads bounds.1 = .structural lowerKind lower)
    (upperAt : state.view.heads bounds.2 = .structural upperKind upper)
    (lowerShape : state.view.shapes lowerKind = shape) (upperShape : state.view.shapes upperKind = shape)
    (known : Input models values state bounds origin term) (explicit : ∀ name, term ≠ .leaf name) :
    ∃ children : Fin shape.arity → Expr Nat, term = .node (.structural shape) children ∧
      InputsAt models values state (fun index => origin.map fun parent => .structural parent shape index) 0
        ((List.ofFn lower).zip (List.ofFn upper)) (List.ofFn children) := by
  obtain ⟨model,present⟩ := inhabited
  obtain ⟨children,equal,_⟩ := GeneralNominalOpenInspectionPositions.structural_inputs state model (valid model present)
    bounds lowerKind upperKind lower upper lowerAt upperAt lowerShape upperShape (known model present) explicit
  refine ⟨children,equal,?_⟩
  intro other holds
  obtain ⟨parts,same,inputs⟩ := GeneralNominalOpenInspectionPositions.structural_inputs state other (valid other holds)
    bounds lowerKind upperKind lower upper lowerAt upperAt lowerShape upperShape (known other holds) explicit
  have identical := node_injective (equal.symm.trans same)
  exact identical ▸ inputs

theorem nominal_inputs (state : GeneralNominalState.State)
    (inhabited : ∃ model, models model)
    (valid : ∀ model, models model → GeneralNominalState.Models state model) (bounds : Bounds state)
    (descriptor : GeneralNominalState.Descriptor state.base.slots) (recorded : state.nominals bounds.1 = some descriptor)
    {intervals : List (Bounds state)} (found : typeArguments descriptor.arguments = some intervals)
    (known : Input models values state bounds origin term) (explicit : ∀ name, term ≠ .leaf name) :
    ∃ children : Fin intervals.length → Expr Nat, term = .node (.nominal descriptor.declaration.name intervals.length) children ∧
      InputsAt models values state
        (fun index => some (.nominal (origin.getD (.source (state.base.source bounds.1))) descriptor.declaration.name index)) 0
        intervals (List.ofFn children) := by
  obtain ⟨model,present⟩ := inhabited
  obtain ⟨children,equal,_⟩ := GeneralNominalOpenInspectionPositions.nominal_inputs state model (valid model present)
    bounds descriptor recorded found (known model present) explicit
  refine ⟨children,equal,?_⟩
  intro other holds
  obtain ⟨parts,same,inputs⟩ := GeneralNominalOpenInspectionPositions.nominal_inputs state other (valid other holds)
    bounds descriptor recorded found (known other holds) explicit
  have identical := node_injective (equal.symm.trans same)
  exact identical ▸ inputs

/-- Both nominal endpoint reports describe the same actual finite input.
Their interval endpoints can remain distinct. -/
theorem upper_input (state : GeneralNominalState.State)
    (valid : ∀ model, models model → GeneralNominalState.Models state model) (bounds : Bounds state)
    (lower upper : GeneralNominalState.Descriptor state.base.slots)
    (lowerAt : state.nominals bounds.1 = some lower) (upperAt : state.nominals bounds.2 = some upper)
    (known : Input models values state bounds origin term) :
    Input models values state (bounds.2,bounds.2) origin term := by
  intro model holds
  have current := known model holds
  obtain ⟨xs,_,one⟩ := (valid model holds).2.1 bounds.1 lower lowerAt
  obtain ⟨ys,_,two⟩ := (valid model holds).2.1 bounds.2 upper upperAt
  have equal := GeneralNominalIntervalLaws.nominal_sandwich lower.declaration.name upper.declaration.name xs ys
    (denote (values model) term)
    (CommonNominalFullCarrier.subtype_trans one.2 current.2.1.1)
    (CommonNominalFullCarrier.subtype_trans current.2.1.2 two.1)
  exact ⟨current.1,⟨CommonNominalFullCarrier.subtype_trans two.1 equal.2.2,current.2.1.2⟩,current.2.2⟩

end Yulang.GeneralNominalUniformInspectionInputs
