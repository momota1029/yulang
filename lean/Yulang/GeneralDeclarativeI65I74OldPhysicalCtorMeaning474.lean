import Yulang.GeneralDeclarativeI65I74FiniteCtorFixedPoint474
import Yulang.GeneralDeclarativeI65I74AuthenticatedPathSound473

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473
open GeneralDeclarativeHead320 (Equation Models environment)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeAliasMeaning321 (alias_sound)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty)
open ObservationRawAlias471 (ClassWire checkWholeClass connectedKeys checked_class_is_exact_for_every_name)
open ObservationSyntax471 (descend)

def interpretedAt (s : GeneralDeclarativeI65.State) (t : Positions n) (m : Assignment)
    (i : Fin n) : Ty :=
  match oldPosition t i with
  | .logical name => (m name).1
  | .rowPos _ _ => ((readTermAt s t i).map (value (environment m) .actual)).getD .bottom

theorem a_resolved_literal_node_reuses_its_actual_old_row_term
    {s : GeneralDeclarativeI65.State} {t : Positions n} {i : Fin n} {ordinal path expr}
    (site : oldPosition t i = .rowPos ordinal path)
    (read : readTermAt s t i = some expr) :
    ∃ row, s.current.ordinary.equations[ordinal]? = some row ∧
      descend s row.right path = some expr := by
  unfold oldPosition at site
  cases found : s.current.ordinary.equations[(t.cells.get i).oldOrdinal]? with
  | none => simp [readTermAt,site,found,bind,Option.bind] at read
  | some row =>
    by_cases key : ordinal = (t.cells.get i).oldOrdinal
    · subst ordinal
      exact ⟨row,found,by simpa [readTermAt,site,found,bind,Option.bind] using read⟩
    · simp [readTermAt,site,found,key,bind,Option.bind] at read

theorem a_resolved_logical_node_reuses_its_actual_alias_and_physical_owner_row
    {s : GeneralDeclarativeI65.State} {t : Positions n} {i : Fin n} {logical expr}
    (site : oldPosition t i = .logical logical)
    (read : readTermAt s t i = some expr) :
    ∃ row, s.current.ordinary.equations[(t.cells.get i).oldOrdinal]? = some row ∧
      GeneralDeclarativeLowerKnown321.Alias s.current.ordinary logical row.left ∧ row.right = expr := by
  unfold oldPosition at site
  cases obtained : s.current.ordinary.equations[(t.cells.get i).oldOrdinal]? with
  | none => simp [readTermAt,site,obtained,bind,Option.bind] at read
  | some row =>
    simp [readTermAt,site,obtained,bind,Option.bind] at read
    exact ⟨row,rfl,(checked_class_is_exact_for_every_name read.1.1.1 _).mp read.1.1.2,read.2⟩

theorem every_resolved_virtual_node_means_its_literal_term_in_each_old_model
    {s : GeneralDeclarativeI65.State} {t : Positions n} {i : Fin n} {expr}
    (read : readTermAt s t i = some expr) (m : Assignment) (fits : Models s.current.ordinary m) :
    CommonNominalFullCarrier.Equivalent (interpretedAt s t m i) (value (environment m) .actual expr) := by
  cases place : oldPosition t i with
  | logical root =>
    obtain ⟨row,physical,alias,spelling⟩ :=
      a_resolved_logical_node_reuses_its_actual_alias_and_physical_owner_row place read
    have atEquation := fits.2 row (List.mem_of_getElem? physical)
    simpa [interpretedAt,place,spelling] using
      eqv_trans (alias_sound alias m fits) atEquation
  | rowPos _ _ => simp [interpretedAt,place,read,eqv_refl]


open ObservationSyntax471 (Slot ReadsDescription one_step_raw_lexical_position_is_the_actual_selected_operand)

theorem actual_named_or_inline_child_in_one_stored_row_has_exact_old_meaning
    {s : GeneralDeclarativeI65.State} {t : Positions n} {parent child : Fin n}
    {above below : Expr} {which : Slot} {tag fields}
    (readParent : readTermAt s t parent = some above)
    (description : ReadsDescription s above tag fields) (seen : (which,below) ∈ fields)
    (address : oldPosition t child = anchorFor (t.cells.get parent) which below)
    {childExpr} (readChild : readTermAt s t child = some childExpr) (m : Assignment) :
    interpretedAt s t m child = value (environment m) .actual below := by
  have sameInline {ordinal before}
      (coordinate : oldPosition t child = .rowPos ordinal (before ++ [which]))
      {row}
      (physical : s.current.ordinary.equations[ordinal]? = some row)
      (base : descend s row.right before = some above) :
      interpretedAt s t m child = value (environment m) .actual below := by
    obtain ⟨r,exact,content⟩ := a_resolved_literal_node_reuses_its_actual_old_row_term coordinate readChild
    have same := Option.some.inj (physical.symm.trans exact)
    subst r
    have actual := one_step_raw_lexical_position_is_the_actual_selected_operand base description seen
    have sameData := Option.some.inj (actual.symm.trans content)
    simp [interpretedAt,coordinate,readChild,←sameData]
  have recursive (nonVar : ∀ a, below ≠ .variable a) :
      interpretedAt s t m child = value (environment m) .actual below := by
    cases origin : oldPosition t parent with
    | logical key =>
      obtain ⟨row,physical,_,rowTerm⟩ :=
        a_resolved_logical_node_reuses_its_actual_alias_and_physical_owner_row origin readParent
      refine sameInline (before := []) (row := row) ?_ physical ?_
      · unfold oldPosition at origin
        rw [address]
        cases below <;> try {exact (nonVar _ rfl).elim}
        all_goals simp [anchorFor,origin]
      · simp [descend,rowTerm]
    | rowPos ordinal before =>
      obtain ⟨row,physical,raw⟩ := a_resolved_literal_node_reuses_its_actual_old_row_term origin readParent
      apply sameInline (before := before) (row := row) _ physical raw
      unfold oldPosition at origin
      rw [address]
      cases below <;> try {exact (nonVar _ rfl).elim}
      all_goals simp [anchorFor,origin]
  cases below with
  | «variable» name =>
    change interpretedAt s t m child = (m name).1
    simp [interpretedAt,address,anchorFor]
  | primitive | nominal | record | variant | join =>
    exact recursive (fun _ nope => by cases nope)

end Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473


set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeRecordResidual323 (withTail permute_fields)
open GeneralDeclarativeVisibleRecord326 (visible_spine)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open CommonRoleCanonicalRows (normalize normalize_unique)

theorem old_closed_literal_spelling_is_exact_before_shadow_removal
    {raw : Expr} {fields : List (Nat × Expr)} (closed : ClosedFields raw fields) :
    raw = withTail fields (.primitive .emptyRecord []) := by
  induction closed with
  | empty => rfl
  | field _ ih => simp [withTail,←ih]

theorem sorted_first_visible_literal_record_preserves_every_original_value
    {raw : Expr} {fields : List (Nat × Expr)} (closed : ClosedFields raw fields) :
    ∀ m : Assignment, eqAt m raw (withTail (sortedFields fields) (.primitive .emptyRecord [])) := by
  intro m
  rw [old_closed_literal_spelling_is_exact_before_shadow_removal closed]
  exact eqv_trans (visible_spine m fields _)
    (permute_fields m _ (List.mergeSort_perm (normalize fields) (fun a b => a.1 ≤ b.1)).symm (normalize_unique fields))

theorem actual_literal_record_descriptor_has_exact_fitting_ordinary_meaning
    {p : RetainedFull445.FullProblem} {ordinal : Nat} {raw : GeneralDeclarativeHead320.Equation}
    {fields}
    (present : p.state.base.core.current.ordinary.equations[ordinal]? = some raw)
    (actual : ClosedFields raw.right fields) (m : GeneralDeclarativeI65.Model)
    (fit : FitsFull p.state m) :
    eqAt m.assignment (.variable raw.left) (withTail (sortedFields fields) (.primitive .emptyRecord [])) := by
  have old := fit.1.1.1.2 raw (List.mem_of_getElem? present)
  exact eqv_trans old (sorted_first_visible_literal_record_preserves_every_original_value actual m.assignment)

end Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471

namespace Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473
open CommonNominalSyntax (Layer State)
open ObservationSyntax471 (Slot Label ReadsDescription RecordEntries sortedFields description_exact)
open G04FiniteConstructorSemantics473 (Shell formed shellLayer rowLayer)
open GeneralDeclarativeHead320 (Models environment)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Equivalent)
open GeneralDeclarativeRecordResidual323 (withTail)

def byLabel (l : Label) (next : Slot → α) : Shell α :=
  match l with
  | .scalar base => .scalar base
  | .nominal name => .unaryNominal name (next (.argument 0))
  | .structural .pair => .pair (next (.argument 0)) (next (.argument 1))
  | .structural (.record labels) => .row (labels.map fun k => (k,next (.field k)))
  | .structural (.variant tag) => .variant tag (next .variant)
  | .structural .exactEmpty => .exactEmpty

theorem listed_record_child_values_are_the_exact_record_layer
    (m : Assignment) (mapping : Slot → α) (meanings : α → Ty) (fields : List (Nat × Expr))
    (child : ∀ k rhs, (k,rhs) ∈ fields →
      meanings (mapping (.field k)) = value (environment m) .actual rhs) :
    value (environment m) .actual (withTail fields (.primitive .emptyRecord [])) =
      (rowLayer (fields.map (fun x => x.1) |>.map (fun k => (k,mapping (.field k))))).map
        (State.node ∘ meanings) := by
  induction fields with
  | nil => rfl
  | cons top rest ih =>
    obtain ⟨k,e⟩ := top
    have tail := ih (fun a b known => child a b (List.mem_cons_of_mem _ known))
    simp only [withTail,value,List.map_cons,rowLayer,Layer.map,Function.comp_def]
    unfold CommonNominalFullCarrier.record
    rw [←child k e List.mem_cons_self,tail]
    rfl

theorem read_description_denotes_its_exact_shape_from_the_selected_child_values
    {s : GeneralDeclarativeI65.State} {e : Expr} {l : Label} {fields : List (Slot × Expr)}
    (desc : ReadsDescription s e l fields) (m : Assignment) (mapping : Slot → α) (meanings : α → Ty)
    (child : ∀ a rhs, (a,rhs) ∈ fields →
      meanings (mapping a) = value (environment m) .actual rhs) :
    Equivalent (value (environment m) .actual e) (formed (byLabel l mapping) meanings) := by
  cases desc with
  | scalar | empty | exactEmpty => exact eqv_refl _
  | pair =>
    have one := child (.argument 0) _ List.mem_cons_self
    have two := child (.argument 1) _ (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [byLabel,formed,shellLayer,Layer.map,Function.comp_def,one,two]
    exact eqv_refl _
  | declared _ =>
    have one := child (.argument 0) _ List.mem_cons_self
    simp only [byLabel,formed,shellLayer,Layer.map,List.map_cons,List.map_nil,Sum.map_inl,Function.comp_def,one]
    exact eqv_refl _
  | variant =>
    have one := child .variant _ List.mem_cons_self
    simp only [byLabel,formed,shellLayer,Layer.map,Function.comp_def,one]
    exact eqv_refl _
  | record spine =>
    apply eqv_trans (ObservationSyntax471.sorted_first_visible_literal_record_preserves_every_original_value
      (.field spine) m)
    have exact := listed_record_child_values_are_the_exact_record_layer m mapping meanings _
      (fun k e found => child (.field k) e
        (List.mem_map.mpr ⟨(k,e),found,rfl⟩))
    rw [exact]
    exact eqv_refl _


structure TypedObservationAt (s : GeneralDeclarativeI65.State) (t : Positions n)
    (embed : Fin k → Fin n) (node : Fin k) where
  actualTerm : Expr
  exact : readTermAt s t (embed node) = some actualTerm
  head : Label
  fields : List (Slot × Expr)
  authoredDescription : ReadsDescription s actualTerm head fields
  child : Slot → Fin k
  childAddress : ∀ slot term, (slot,term) ∈ fields →
    oldPosition t (embed (child slot)) = anchorFor (t.cells.get (embed node)) slot term

def typedBy (table : (i : Fin k) → TypedObservationAt s t embed i) :
    Fin k → Shell (Fin k) :=
  fun i => byLabel (table i).head (table i).child

theorem every_original_model_is_compatible_with_the_same_finite_closed_typed_graph
    {s : GeneralDeclarativeI65.State} {t : Positions n} {embed : Fin k → Fin n}
    (nodes : (i : Fin k) → TypedObservationAt s t embed i) :
    ∀ m : Assignment, Models s.current.ordinary m →
      ∀ i, Equivalent (interpretedAt s t m (embed i))
        (G04FiniteConstructorSemantics473.value (typedBy nodes) i) := by
  intro m fits
  apply G04FiniteConstructorSemantics473.all_satisfying_assignments_have_the_same_regular_constructor_value
  intro i
  have reads := (nodes i).exact
  have model := every_resolved_virtual_node_means_its_literal_term_in_each_old_model reads m fits
  have shell := read_description_denotes_its_exact_shape_from_the_selected_child_values
    (nodes i).authoredDescription m (nodes i).child (fun j => interpretedAt s t m (embed j))
    (fun slot raw found => actual_named_or_inline_child_in_one_stored_row_has_exact_old_meaning
      reads (nodes i).authoredDescription found ((nodes i).childAddress slot raw found)
      (nodes ((nodes i).child slot)).exact m)
  exact eqv_trans model shell

theorem same_fits_full_input_keeps_unchanged_typed_observation_graph
    {p : RetainedFull445.FullProblem} {t : Positions n} {embed : Fin k → Fin n}
    (nodes : (i : Fin k) → TypedObservationAt p.old.state.core t embed i)
    (m : GeneralDeclarativeI65.Model) (fit : FitsFull p.state m) :
    ∀ i, Equivalent (interpretedAt p.old.state.core t m.assignment (embed i))
      (G04FiniteConstructorSemantics473.value (typedBy nodes) i) :=
  every_original_model_is_compatible_with_the_same_finite_closed_typed_graph nodes m.assignment fit.1.1.1

end Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473
