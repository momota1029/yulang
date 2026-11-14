import Yulang.GeneralNominalUniformHoleLabels

/-! Nominal readback through explicit actual-argument names. Parameter
intervals may be strict. Model predicates are parameters so centered sources
can supply their own uniform provenance without identifying the endpoints. -/
namespace Yulang.GeneralNominalNamedArgumentReadback
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection GeneralNominalIndexedHoleReadback
open GeneralNominalHoleElimination GeneralNominalSaturationState GeneralNominalBackedHoleElimination
open GeneralNominalFeedbackK2 GeneralNominalSourceHoleExposure

variable {roles : Roles.RoleDecls}
variable {models : GeneralNominalCommonBridge.Assignment → Prop} {holeSources : Nat → Nat}

def Centers (models : GeneralNominalCommonBridge.Assignment → Prop) (parent : Origin)
    (name count : Nat) (identities : Fin count → Nat) : Prop :=
  ∀ position model, models model → Same model (.nominal parent name position.val) (.source (identities position))

theorem center_fits (state : GeneralNominalState.State)
    (valid : ∀ model, models model → GeneralNominalState.Models state model)
    (parent : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals parent = some descriptor) (intervals : List (GeneralNominalInspection.Bounds state))
    (found : typeArguments descriptor.arguments = some intervals)
    {identities : Fin intervals.length → Nat}
    (centers : Centers models (.source (state.base.source parent)) descriptor.declaration.name intervals.length identities) :
    ∀ position : Fin intervals.length, ∀ model, models model →
      Fits state model intervals[position] (model (identities position)).1 := by
  intro position model holds
  have parameter : descriptor.arguments[position.val]? = some (.type intervals[position]) := by
    rw [GeneralNominalInspectionFiniteValues.type_arguments _ found]
    simp only [List.getElem?_map,List.getElem?_eq_getElem position.isLt,Option.map_some,Fin.getElem_fin]
  obtain ⟨⟨actual,seen⟩,bounded⟩ := nominal_argument_bounds state model (valid model holds) parent descriptor recorded
    position.val intervals[position] parameter
  have equal := (centers position model holds).2.2 actual _ seen (.source _)
  exact ⟨CommonNominalFullCarrier.subtype_trans (bounded actual seen).1 equal.1,
    CommonNominalFullCarrier.subtype_trans equal.2 (bounded actual seen).2⟩

theorem nominal_head (state : GeneralNominalState.State)
    (valid : ∀ model, models model → GeneralNominalState.Models state model)
    (parent : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals parent = some descriptor) (intervals : List (GeneralNominalInspection.Bounds state))
    (found : typeArguments descriptor.arguments = some intervals) :
    ∀ model, models model → Head model (.source (state.base.source parent))
      (.nominal descriptor.declaration.name intervals.length) := by
  intro model holds
  refine ⟨⟨_,.source _⟩,?_⟩
  intro actual seen
  cases seen
  obtain ⟨values,fits,equal⟩ := (valid model holds).2.1 parent descriptor recorded
  have length := fits
  rw [GeneralNominalInspectionFiniteValues.type_arguments _ found] at length
  have length := GeneralNominalInspectionFiniteValues.fits_types_length length
  exact ⟨values,by simpa only [List.length_map] using length.symm,equal⟩

/-- Uniform children are interpreted at the named actual arguments. The
source origin map and remaining holes are the original ones. -/
theorem nominal_readback (state : GeneralNominalState.State)
    (valid : ∀ model, models model → GeneralNominalState.Models state model)
    (parent : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals parent = some descriptor) (intervals : List (GeneralNominalInspection.Bounds state))
    (found : typeArguments descriptor.arguments = some intervals)
    {identities : Fin intervals.length → Nat}
    (centers : Centers models (.source (state.base.source parent)) descriptor.declaration.name intervals.length identities)
    (terms : Fin intervals.length → Expr Nat)
    (known : ∀ position, Readback models origins remaining (.source (identities position)) (terms position)) :
    Readback models origins remaining (.source (state.base.source parent))
      (.node (.nominal descriptor.declaration.name intervals.length) terms) := by
  constructor
  · intro model holds
    exact ⟨nominal_head state valid parent descriptor recorded intervals found model holds,
      fun position => holds_transport (same_symm (centers position model holds)) ((known position).1 model holds)⟩
  · intro name member
    obtain ⟨parts,listed,present⟩ := List.mem_flatten.mp member
    obtain ⟨position,rfl⟩ := List.mem_ofFn.mp listed
    exact (known position).2 name present

theorem named_argument (state : State roles)
    (centers : Centers (Models state) (.source parent) name count identities) (position : Fin count) :
    Argument state parent (identities position) := by
  refine ⟨name,position.val,?_⟩
  intro model valid
  obtain ⟨actual,seen⟩ := (centers position model valid).1
  exact ⟨actual,recover_observation model (.argument (.source parent) name position.val) actual seen,
    (centers position model valid).2.2 actual _ seen (.source _)⟩

theorem nominal_backed (state : State roles)
    (centers : Centers (Models state) (.source parent) name count identities)
    (parentMember : parent ∈ GeneralNominalState.sources state.context.state)
    (centerMembers : ∀ position, identities position ∈ GeneralNominalState.sources state.context.state)
    (terms : Fin count → Expr Nat)
    (known : ∀ position, Backed state holeSources (identities position) (terms position)) :
    Backed state holeSources parent (.node (.nominal name count) terms) :=
  .node _ _ identities (fun position => ⟨parentMember,centerMembers position,Or.inr (named_argument state centers position)⟩) known

/-- Existing source-key templates compose with centered nominal readback.
No catalogue key is reconstructed from the semantic nominal name. -/
theorem labelled_readback (state : GeneralNominalState.State)
    (valid : ∀ model, models model → GeneralNominalState.Models state model)
    (parent : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals parent = some descriptor) (intervals : List (GeneralNominalInspection.Bounds state))
    (found : typeArguments descriptor.arguments = some intervals)
    {identities : Fin intervals.length → Nat}
    (centers : Centers models (.source (state.base.source parent)) descriptor.declaration.name intervals.length identities)
    (terms : Fin intervals.length → Expr Nat)
    (known : ∀ position, Readback models origins remaining (.source (identities position)) (terms position))
    (label : GeneralNominalOpenPatternLabels.Label context pattern
      (.node (.nominal descriptor.declaration.name intervals.length) terms)) :
    GeneralNominalUniformHoleLabels.Labelled models context origins remaining (.source (state.base.source parent)) pattern
      (.node (.nominal descriptor.declaration.name intervals.length) terms) :=
  ⟨label,nominal_readback state valid parent descriptor recorded intervals found centers terms known⟩

/-- Transport a projected actual argument through an established parent
alias; the nominal body is never inspected. -/
theorem nominal_observation_transport {index : Nat} (same : Same model first last)
    (seen : Observes model (.nominal first name index) value) :
    Observes model (.nominal last name index) value := by
  obtain ⟨other,observed⟩ := same.2.1
  cases seen with
  | nominal parent equal found =>
    have parents := same.2.2 _ _ parent observed
    exact .nominal observed
      ⟨CommonNominalFullCarrier.subtype_trans parents.2 equal.1,
        CommonNominalFullCarrier.subtype_trans equal.2 parents.1⟩ found

theorem centers_transport (same : ∀ model, models model → Same model first last)
    (centers : Centers models first name count identities) : Centers models last name count identities := by
  intro position model valid
  apply holds_observations (.leaf (.source (identities position))) _ (centers position model valid)
  intro value
  exact ⟨nominal_observation_transport (same model valid),nominal_observation_transport (same_symm (same model valid))⟩

/-- Same-head nominal endpoint observations identify their nominal root
values with a supplied actual center. No equality of argument endpoints is
assumed or concluded. -/
theorem nominal_fallback_parents (state : GeneralNominalState.State)
    (valid : ∀ model, models model → GeneralNominalState.Models state model)
    (bounds : GeneralNominalInspection.Bounds state)
    (lower upper : GeneralNominalState.Descriptor state.base.slots)
    (lowerAt : state.nominals bounds.1 = some lower) (upperAt : state.nominals bounds.2 = some upper)
    (fits : ∀ model, models model → Fits state model bounds (model center).1) :
    (∀ model, models model → Same model (.source center) (.source (state.base.source bounds.1))) ∧
    (∀ model, models model → Same model (.source center) (.source (state.base.source bounds.2))) := by
  have both : ∀ model, models model →
      CommonNominalFullCarrier.Equivalent (model center).1 (model (state.base.source bounds.1)).1 ∧
      CommonNominalFullCarrier.Equivalent (model center).1 (model (state.base.source bounds.2)).1 := by
    intro model holds
    obtain ⟨xs,_,one⟩ := (valid model holds).2.1 bounds.1 lower lowerAt
    obtain ⟨ys,_,two⟩ := (valid model holds).2.1 bounds.2 upper upperAt
    have equal := GeneralNominalIntervalLaws.nominal_sandwich _ _ xs ys (model center).1
      (CommonNominalFullCarrier.subtype_trans one.2 (fits model holds).1)
      (CommonNominalFullCarrier.subtype_trans (fits model holds).2 two.1)
    exact ⟨⟨CommonNominalFullCarrier.subtype_trans equal.1.1 one.2,
        CommonNominalFullCarrier.subtype_trans one.1 equal.1.2⟩,
      ⟨CommonNominalFullCarrier.subtype_trans equal.2.1 two.2,
        CommonNominalFullCarrier.subtype_trans two.1 equal.2.2⟩⟩
  constructor <;> intro model holds <;> refine ⟨⟨_,.source _⟩,⟨_,.source _⟩,?_⟩
  · intro first last one two; cases one; cases two; exact (both model holds).1
  · intro first last one two; cases one; cases two; exact (both model holds).2

theorem nominal_fallback_centers (state : GeneralNominalState.State)
    (valid : ∀ model, models model → GeneralNominalState.Models state model)
    (bounds : GeneralNominalInspection.Bounds state)
    (lower upper : GeneralNominalState.Descriptor state.base.slots)
    (lowerAt : state.nominals bounds.1 = some lower) (upperAt : state.nominals bounds.2 = some upper)
    (fits : ∀ model, models model → Fits state model bounds (model center).1)
    (centers : Centers models (.source center) name count identities) :
    Centers models (.source (state.base.source bounds.1)) name count identities ∧
      Centers models (.source (state.base.source bounds.2)) name count identities := by
  have parents := nominal_fallback_parents state valid bounds lower upper lowerAt upperAt fits
  exact ⟨centers_transport parents.1 centers,centers_transport parents.2 centers⟩

theorem nominal_discharge (state : State roles) (parent : Fin state.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.context.state.base.slots)
    (recorded : state.context.state.nominals parent = some descriptor)
    (intervals : List (GeneralNominalInspection.Bounds state.context.state))
    (found : typeArguments descriptor.arguments = some intervals)
    {identities : Fin intervals.length → Nat}
    (centers : Centers (Models state) (.source (state.context.state.base.source parent)) descriptor.declaration.name intervals.length identities)
    (centerMembers : ∀ position, identities position ∈ GeneralNominalState.sources state.context.state)
    (terms : Fin intervals.length → Expr Nat)
    (old : Readback (Models state) (fun name => .source (holeSources name)) remaining
      (.source (state.context.state.base.source parent)) (.leaf hole))
    (known : ∀ position, Readback (Models state) (fun name => .source (holeSources name)) remaining
      (.source (identities position)) (terms position))
    (backed : ∀ position, Backed state holeSources (identities position) (terms position))
    (inhabited : ∃ model, Models state model)
    (safe : ¬ RecursAt state (state.context.state.base.source parent)) :
    hole ∈ remaining ∧ Readback (Models state) (fun name => .source (holeSources name)) (remaining.erase hole)
      (.source (holeSources hole)) (.node (.nominal descriptor.declaration.name intervals.length) terms) :=
  GeneralNominalReducedHoleSources.discharge old
    (nominal_readback state.context.state (fun _ valid => valid.1) parent descriptor recorded intervals found centers terms known)
    (nominal_backed state centers (slot_source _ parent) centerMembers terms backed) inhabited safe

end Yulang.GeneralNominalNamedArgumentReadback
