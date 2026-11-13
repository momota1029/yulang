import Yulang.GeneralNominalFrontierValuations

/-! Direct source observations produce genuine indexed replacements. At a
noncyclic inhabited structural root no immediate child reuses that root's
source index, so its constructor can delete that fixed hole globally. -/
namespace Yulang.GeneralNominalSourceHoleExposure
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalSourceFrontier
open GeneralNominalIndexedHoleReadback GeneralNominalHoleElimination GeneralNominalSharedEnumeration
open GeneralNominalSaturationState GeneralNominalActualInspectionSteps GeneralNominalReadbackFunctionality

variable {roles : Roles.RoleDecls}

theorem slot_source (state : GeneralNominalState.State) (slot : Fin state.base.slots) :
    state.base.source slot ∈ GeneralNominalState.sources state :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩)))

theorem slot_frontier (state : GeneralNominalState.State) (slot : Fin state.base.slots) :
    Origin.source (state.base.source slot) ∈ frontier state := source_member (slot_source state slot)

def structuralTerm (state : GeneralNominalState.State) (kind : Fin state.view.kinds)
    (children : Fin (state.view.shapes kind).arity → Fin state.base.slots) : Expr Nat :=
  .node (.structural (state.view.shapes kind))
    (fun i => .leaf (index (frontier state) (state.base.source (children i))))

theorem structural_readback (state : State roles) (parent : Fin state.context.state.base.slots)
    (kind : Fin state.context.state.view.kinds)
    (children : Fin (state.context.state.view.shapes kind).arity → Fin state.context.state.base.slots)
    (recorded : state.context.state.view.heads parent = .structural kind children) :
    Readback (Models state) (origin (frontier state.context.state)) (holes (frontier state.context.state))
      (.source (state.context.state.base.source parent)) (structuralTerm state.context.state kind children) := by
  constructor
  · intro model valid
    refine ⟨⟨⟨_,.source _⟩,?_⟩,?_⟩
    · intro actual seen
      cases seen
      refine ⟨List.ofFn (fun i => (model (state.context.state.base.source (children i))).1),List.length_ofFn ..,?_⟩
      exact GeneralNominalFiniteBracket.structural_slot state.context.state model valid.1 parent kind children recorded rfl
    · intro i
      change Same model (.structural (.source (state.context.state.base.source parent)) (state.context.state.view.shapes kind) i.val)
        (origin (frontier state.context.state) (index (frontier state.context.state) (state.context.state.base.source (children i))))
      rw [index_origin (slot_frontier state.context.state (children i))]
      exact GeneralNominalStructuralReadback.actual_structural_readback state parent kind children recorded i model valid
  · intro name member
    obtain ⟨entries,listed,present⟩ := List.mem_flatten.mp member
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp listed
    cases List.mem_singleton.mp present
    exact List.mem_range.mpr (List.idxOf_lt_length_of_mem (slot_frontier state.context.state (children i)))

theorem structural_canonical (state : GeneralNominalState.State) (kind : Fin state.view.kinds)
    (children : Fin (state.view.shapes kind).arity → Fin state.base.slots) :
    Canonical (structuralTerm state kind children) := ⟨state.view.canonical kind,fun _ => True.intro⟩

theorem child_different (state : State roles) (parent : Fin state.context.state.base.slots)
    (kind : Fin state.context.state.view.kinds)
    (children : Fin (state.context.state.view.shapes kind).arity → Fin state.context.state.base.slots)
    (recorded : state.context.state.view.heads parent = .structural kind children)
    (inhabited : ∃ model, Models state model)
    (safe : ¬ GeneralNominalFeedbackK2.RecursAt state (state.context.state.base.source parent))
    (position : Fin (state.context.state.view.shapes kind).arity) :
    state.context.state.base.source (children position) ≠ state.context.state.base.source parent := by
  intro same
  apply safe
  refine ⟨⟨_,?_,.nil _⟩,inhabited⟩
  refine ⟨slot_source _ parent,slot_source _ parent,Or.inl ⟨parent,children position,?_,?_,?_⟩⟩
  · exact ⟨kind,children,recorded,position,rfl⟩
  · exact GeneralNominalFeedbackK2.equal_refl state _
  · rw [same]; exact GeneralNominalFeedbackK2.equal_refl state _

theorem structural_replacement (state : State roles) (parent : Fin state.context.state.base.slots)
    (kind : Fin state.context.state.view.kinds)
    (children : Fin (state.context.state.view.shapes kind).arity → Fin state.context.state.base.slots)
    (recorded : state.context.state.view.heads parent = .structural kind children)
    (inhabited : ∃ model, Models state model)
    (safe : ¬ GeneralNominalFeedbackK2.RecursAt state (state.context.state.base.source parent)) :
    Readback (Models state) (origin (frontier state.context.state))
      ((holes (frontier state.context.state)).erase (index (frontier state.context.state) (state.context.state.base.source parent)))
      (origin (frontier state.context.state) (index (frontier state.context.state) (state.context.state.base.source parent)))
      (structuralTerm state.context.state kind children) := by
  have readback := structural_readback state parent kind children recorded
  rw [index_origin (slot_frontier state.context.state parent)]
  refine ⟨readback.1,?_⟩
  intro name member
  apply (List.mem_erase_of_ne ?_).mpr (readback.2 name member)
  obtain ⟨entries,listed,present⟩ := List.mem_flatten.mp member
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp listed
  cases List.mem_singleton.mp present
  intro same
  have origins := congrArg (origin (frontier state.context.state)) same
  rw [index_origin (slot_frontier state.context.state (children i)),index_origin (slot_frontier state.context.state parent)] at origins
  exact child_different state parent kind children recorded inhabited safe i (Origin.source.inj origins)

/-- This is one actual source-observation case of Trace extraction, with
replacement height one and exactly one consumed fixed source index. -/
theorem structural_trace (state : State roles) (parent : Fin state.context.state.base.slots)
    (kind : Fin state.context.state.view.kinds)
    (children : Fin (state.context.state.view.shapes kind).arity → Fin state.context.state.base.slots)
    (recorded : state.context.state.view.heads parent = .structural kind children)
    (inhabited : ∃ model, Models state model)
    (safe : ¬ GeneralNominalFeedbackK2.RecursAt state (state.context.state.base.source parent))
    (inventory : Inventory) (initialHoles : inventory.holes = holes (frontier state.context.state))
    (vocabulary : Test.structural (state.context.state.view.shapes kind) ∈ tests) :
    Trace tests (fun _ => 1) inventory
      (eliminate inventory (index (frontier state.context.state) (state.context.state.base.source parent))
        (structuralTerm state.context.state kind children) 1) 1 := by
  have readback := structural_replacement state parent kind children recorded inhabited safe
  apply Trace.next _ _
  · rw [initialHoles]
    exact List.mem_range.mpr (List.idxOf_lt_length_of_mem (slot_frontier state.context.state parent))
  · rw [initialHoles]; exact readback.2
  · apply Bounded.node _ _ vocabulary
    intro i
    apply Bounded.leaf
    rw [initialHoles]
    exact readback.2 _ (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,List.mem_singleton_self _⟩)
  · exact .refl _

def nominalTerm (state : GeneralNominalState.State) (name : Nat) (slots : List (Fin state.base.slots)) : Expr Nat :=
  .node (.nominal name slots.length)
    (fun i => .leaf (index (frontier state) (state.base.source (slots[i.val]'i.isLt))))

theorem point_parameter (descriptor : GeneralNominalState.Descriptor slots)
    (points : List (Fin slots))
    (found : typeArguments descriptor.arguments = some (points.map fun slot => (slot,slot)))
    (position : Fin points.length) :
    descriptor.arguments[position.val]? = some (.type (points[position],points[position])) := by
  rw [GeneralNominalInspectionFiniteValues.type_arguments _ found]
  simp only [List.getElem?_map,List.getElem?_eq_getElem position.isLt,Option.map_some]
  rfl

theorem nominal_readback (state : State roles) (parent : Fin state.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.context.state.base.slots)
    (recorded : state.context.state.nominals parent = some descriptor)
    (points : List (Fin state.context.state.base.slots))
    (found : typeArguments descriptor.arguments = some (points.map fun slot => (slot,slot))) :
    Readback (Models state) (origin (frontier state.context.state)) (holes (frontier state.context.state))
      (.source (state.context.state.base.source parent)) (nominalTerm state.context.state descriptor.declaration.name points) := by
  constructor
  · intro model valid
    refine ⟨⟨⟨_,.source _⟩,?_⟩,?_⟩
    · intro actual seen
      cases seen
      obtain ⟨values,fits,equal⟩ := valid.1.2.1 parent descriptor recorded
      have length := fits
      rw [GeneralNominalInspectionFiniteValues.type_arguments _ found] at length
      have length := GeneralNominalInspectionFiniteValues.fits_types_length length
      refine ⟨values,?_,equal⟩
      simpa only [List.length_map] using length.symm
    · intro i
      change Same model (.nominal (.source (state.context.state.base.source parent)) descriptor.declaration.name i.val)
        (origin (frontier state.context.state) (index (frontier state.context.state) (state.context.state.base.source (points[i.val]'i.isLt))))
      rw [index_origin (slot_frontier state.context.state (points[i.val]'i.isLt))]
      exact point_argument_readback state parent (points[i.val]'i.isLt) descriptor recorded (point_parameter descriptor points found i) model valid
  · intro name member
    obtain ⟨entries,listed,present⟩ := List.mem_flatten.mp member
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp listed
    cases List.mem_singleton.mp present
    exact List.mem_range.mpr (List.idxOf_lt_length_of_mem (slot_frontier state.context.state (points[i.val]'i.isLt)))

theorem nominal_replacement (state : State roles) (parent : Fin state.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.context.state.base.slots)
    (recorded : state.context.state.nominals parent = some descriptor)
    (points : List (Fin state.context.state.base.slots))
    (found : typeArguments descriptor.arguments = some (points.map fun slot => (slot,slot)))
    (inhabited : ∃ model, Models state model)
    (safe : ¬ GeneralNominalFeedbackK2.RecursAt state (state.context.state.base.source parent)) :
    Readback (Models state) (origin (frontier state.context.state))
      ((holes (frontier state.context.state)).erase (index (frontier state.context.state) (state.context.state.base.source parent)))
      (origin (frontier state.context.state) (index (frontier state.context.state) (state.context.state.base.source parent)))
      (nominalTerm state.context.state descriptor.declaration.name points) := by
  have readback := nominal_readback state parent descriptor recorded points found
  rw [index_origin (slot_frontier state.context.state parent)]
  refine ⟨readback.1,?_⟩
  intro name member
  apply (List.mem_erase_of_ne ?_).mpr (readback.2 name member)
  obtain ⟨entries,listed,present⟩ := List.mem_flatten.mp member
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp listed
  cases List.mem_singleton.mp present
  intro same
  have origins := congrArg (origin (frontier state.context.state)) same
  rw [index_origin (slot_frontier state.context.state (points[i.val]'i.isLt)),index_origin (slot_frontier state.context.state parent)] at origins
  have identical := Origin.source.inj origins
  have argument := GeneralNominalFeedbackK2.endpoint_argument state parent (points[i.val]'i.isLt) (points[i.val]'i.isLt) descriptor recorded i.val
    (point_parameter descriptor points found i) (GeneralNominalFeedbackK2.equal_refl state _)
  rw [identical] at argument
  obtain ⟨model,valid⟩ := inhabited
  exact safe (GeneralNominalFeedbackK2.self_argument_cycle state _ (slot_source _ parent) argument model valid)

end Yulang.GeneralNominalSourceHoleExposure
