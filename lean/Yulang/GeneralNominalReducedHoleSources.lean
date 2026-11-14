import Yulang.GeneralNominalBackedHoleElimination

/-! Source constructor producers over a reduced original hole set. Immediate
children can already have compound readbacks. No later slot is made a new
hole and the finite original origin map is kept unchanged. -/
namespace Yulang.GeneralNominalReducedHoleSources
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalSourceHoleExposure
open GeneralNominalIndexedHoleReadback GeneralNominalHoleElimination GeneralNominalSaturationState
open GeneralNominalBackedHoleElimination GeneralNominalFeedbackK2 GeneralNominalReadbackFunctionality

variable {roles : Roles.RoleDecls} {identities : Nat → Nat}

theorem structural_readback (state : State roles) (parent : Fin state.context.state.base.slots)
    (kind : Fin state.context.state.view.kinds)
    (children : Fin (state.context.state.view.shapes kind).arity → Fin state.context.state.base.slots)
    (recorded : state.context.state.view.heads parent = .structural kind children)
    (terms : Fin (state.context.state.view.shapes kind).arity → Expr Nat)
    (known : ∀ position, Readback (Models state) origins remaining
      (.source (state.context.state.base.source (children position))) (terms position)) :
    Readback (Models state) origins remaining (.source (state.context.state.base.source parent))
      (.node (.structural (state.context.state.view.shapes kind)) terms) := by
  constructor
  · intro model valid
    refine ⟨(GeneralNominalSourceHoleExposure.structural_readback state parent kind children recorded).1 model valid |>.1,?_⟩
    intro position
    exact holds_transport
      (same_symm (GeneralNominalStructuralReadback.actual_structural_readback state parent kind children recorded position model valid))
      ((known position).1 model valid)
  · intro name member
    obtain ⟨parts,listed,present⟩ := List.mem_flatten.mp member
    obtain ⟨position,rfl⟩ := List.mem_ofFn.mp listed
    exact (known position).2 name present

theorem structural_backed (state : State roles) (parent : Fin state.context.state.base.slots)
    (kind : Fin state.context.state.view.kinds)
    (children : Fin (state.context.state.view.shapes kind).arity → Fin state.context.state.base.slots)
    (recorded : state.context.state.view.heads parent = .structural kind children)
    (terms : Fin (state.context.state.view.shapes kind).arity → Expr Nat)
    (known : ∀ position, Backed state identities (state.context.state.base.source (children position)) (terms position)) :
    Backed state identities (state.context.state.base.source parent)
      (.node (.structural (state.context.state.view.shapes kind)) terms) := by
  refine .node _ _ (fun position => state.context.state.base.source (children position)) ?_ known
  intro position
  exact ⟨slot_source _ parent,slot_source _ (children position),Or.inl
    ⟨parent,children position,⟨kind,children,recorded,position,rfl⟩,equal_refl _ _,equal_refl _ _⟩⟩

theorem nominal_readback (state : State roles) (parent : Fin state.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.context.state.base.slots)
    (recorded : state.context.state.nominals parent = some descriptor)
    (points : List (Fin state.context.state.base.slots))
    (found : typeArguments descriptor.arguments = some (points.map fun slot => (slot,slot)))
    (terms : Fin points.length → Expr Nat)
    (known : ∀ position, Readback (Models state) origins remaining
      (.source (state.context.state.base.source (points[position.val]'position.isLt))) (terms position)) :
    Readback (Models state) origins remaining (.source (state.context.state.base.source parent))
      (.node (.nominal descriptor.declaration.name points.length) terms) := by
  constructor
  · intro model valid
    refine ⟨(GeneralNominalSourceHoleExposure.nominal_readback state parent descriptor recorded points found).1 model valid |>.1,?_⟩
    intro position
    exact holds_transport (same_symm
      (GeneralNominalActualInspectionSteps.point_argument_readback state parent (points[position.val]'position.isLt) descriptor recorded
        (point_parameter descriptor points found position) model valid)) ((known position).1 model valid)
  · intro name member
    obtain ⟨parts,listed,present⟩ := List.mem_flatten.mp member
    obtain ⟨position,rfl⟩ := List.mem_ofFn.mp listed
    exact (known position).2 name present

theorem nominal_backed (state : State roles) (parent : Fin state.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.context.state.base.slots)
    (recorded : state.context.state.nominals parent = some descriptor)
    (points : List (Fin state.context.state.base.slots))
    (found : typeArguments descriptor.arguments = some (points.map fun slot => (slot,slot)))
    (terms : Fin points.length → Expr Nat)
    (known : ∀ position, Backed state identities (state.context.state.base.source (points[position.val]'position.isLt)) (terms position)) :
    Backed state identities (state.context.state.base.source parent)
      (.node (.nominal descriptor.declaration.name points.length) terms) := by
  refine .node _ _ (fun position => state.context.state.base.source (points[position.val]'position.isLt)) ?_ known
  intro position
  exact ⟨slot_source _ parent,slot_source _ (points[position.val]'position.isLt),Or.inr
    (endpoint_argument state parent (points[position.val]'position.isLt) (points[position.val]'position.isLt) descriptor recorded position.val
      (point_parameter descriptor points found position) (equal_refl _ _))⟩

theorem leaf_equal (old : Readback (Models state) (fun name => .source (identities name)) remaining
    (.source root) (.leaf hole)) : Equal state root (identities hole) := by
  intro model valid
  exact (old.1 model valid).2.2 _ _ (.source _) (.source _)

/-- Direct constructor exposure now produces a replacement over surviving
holes. The occurs check is discharged by the actual graph-backed children. -/
theorem discharge (old : Readback (Models state) (fun name => .source (identities name)) remaining
      (.source root) (.leaf hole))
    (expanded : Readback (Models state) (fun name => .source (identities name)) remaining
      (.source root) (.node test children))
    (backed : Backed state identities root (.node test children))
    (inhabited : ∃ model, Models state model) (safe : ¬ RecursAt state root) :
    hole ∈ remaining ∧ Readback (Models state) (fun name => .source (identities name)) (remaining.erase hole)
      (.source (identities hole)) (.node test children) := by
  refine ⟨old.2 hole (List.mem_singleton_self _),?_,?_⟩
  · intro model valid
    exact holds_transport (old.1 model valid) (expanded.1 model valid)
  · exact safe_closed backed (leaf_equal old) inhabited safe expanded.2

theorem structural_discharge (state : State roles) (parent : Fin state.context.state.base.slots)
    (kind : Fin state.context.state.view.kinds)
    (children : Fin (state.context.state.view.shapes kind).arity → Fin state.context.state.base.slots)
    (recorded : state.context.state.view.heads parent = .structural kind children)
    (terms : Fin (state.context.state.view.shapes kind).arity → Expr Nat)
    (old : Readback (Models state) (fun name => .source (identities name)) remaining
      (.source (state.context.state.base.source parent)) (.leaf hole))
    (known : ∀ position, Readback (Models state) (fun name => .source (identities name)) remaining
      (.source (state.context.state.base.source (children position))) (terms position))
    (backed : ∀ position, Backed state identities (state.context.state.base.source (children position)) (terms position))
    (inhabited : ∃ model, Models state model)
    (safe : ¬ RecursAt state (state.context.state.base.source parent)) :
    hole ∈ remaining ∧ Readback (Models state) (fun name => .source (identities name)) (remaining.erase hole)
      (.source (identities hole)) (.node (.structural (state.context.state.view.shapes kind)) terms) :=
  discharge old (structural_readback state parent kind children recorded terms known)
    (structural_backed state parent kind children recorded terms backed) inhabited safe

theorem nominal_discharge (state : State roles) (parent : Fin state.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.context.state.base.slots)
    (recorded : state.context.state.nominals parent = some descriptor)
    (points : List (Fin state.context.state.base.slots))
    (found : typeArguments descriptor.arguments = some (points.map fun slot => (slot,slot)))
    (terms : Fin points.length → Expr Nat)
    (old : Readback (Models state) (fun name => .source (identities name)) remaining
      (.source (state.context.state.base.source parent)) (.leaf hole))
    (known : ∀ position, Readback (Models state) (fun name => .source (identities name)) remaining
      (.source (state.context.state.base.source (points[position.val]'position.isLt))) (terms position))
    (backed : ∀ position, Backed state identities (state.context.state.base.source (points[position.val]'position.isLt)) (terms position))
    (inhabited : ∃ model, Models state model)
    (safe : ¬ RecursAt state (state.context.state.base.source parent)) :
    hole ∈ remaining ∧ Readback (Models state) (fun name => .source (identities name)) (remaining.erase hole)
      (.source (identities hole)) (.node (.nominal descriptor.declaration.name points.length) terms) :=
  discharge old (nominal_readback state parent descriptor recorded points found terms known)
    (nominal_backed state parent descriptor recorded points found terms backed) inhabited safe

end Yulang.GeneralNominalReducedHoleSources
