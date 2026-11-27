import Yulang.GeneralDeclarativeI65I74ProjectionCutExact464
import Yulang.GeneralDeclarativeI65I74ProjectionDerivation464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464
open GeneralDeclarativeHead320 (Equation Models)
private abbrev RawState := GeneralDeclarativeHead320.State
open GeneralDeclarativeK2Graph321 (Shape Path)
open GeneralDeclarativeK2Graph321.AddAtOneSource
open GeneralDeclarativeGraphRows321 (structural observed shapeOf)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeEqualities322 (Derives semantic)
open GeneralDeclarativeWitnessLiteral349 (sameRows rows_exact)
open List410 (ExactEscapeWire)
open Derivation (EqWire checkEq exact_finite_data_eq_check_iff_independent_Derives453)

/-- Data for checking an already supplied pair of snapshots. The proposed
row is intentionally *not* in the wire: it is obtained from its exact physical
index in the supplied second snapshot. No namespace allocation or state change. -/
structure ProjectionWire where
  equality : EqWire
  cut : ExactEscapeWire

def exactOrderedAppend (before after : RawState) (e : Equation) : Bool :=
  (decide (before.normal.ordinary = after.normal.ordinary) &&
   decide (before.normal.intervals = after.normal.intervals)) &&
   sameRows (before.equations ++ [e]) after.equations

theorem checks_single_ordered_extension_exactly (before after : RawState) (e : Equation) :
    exactOrderedAppend before after e = true ↔ after = extendedRows before e := by
  rcases before with ⟨⟨a,b⟩,old⟩
  rcases after with ⟨⟨c,d⟩,new⟩
  simp only [exactOrderedAppend,Bool.and_eq_true,decide_eq_true_eq,rows_exact]
  constructor
  · rintro ⟨⟨rfl,rfl⟩,rfl⟩
    rfl
  · intro equal
    cases equal
    exact ⟨⟨rfl,rfl⟩,rfl⟩

def checkProjection (before after : RawState) (site : Nat) (w : ProjectionWire) : Bool :=
  match after.equations[before.equations.length]? with
  | none => false
  | some row =>
    exactOrderedAppend before after row &&
      (decide (row.left = site) &&
        checkEq before (.variable site) row.right w.equality &&
        checksNamedProjectionCut before site row.right w.cut)

def ProjectionAt (before after : RawState) (site : Nat) : Prop :=
  ∃ term form, after = extendedRows before ⟨site,term⟩ ∧
    shapeOf term = some form ∧ Derives before (.variable site) term ∧
    (¬ AliasCycle before (observed before) site) ∧
    ∀ child ∈ form.children, ∀ last, GeneralDeclarativeLowerKnown321.Alias before last site →
      ¬ Path (structural before) child last

theorem independent_one_row_projection_iff_finite_data
    (before after : RawState) (site : Nat) :
    (∃ w, checkProjection before after site w = true) ↔ ProjectionAt before after site := by
  constructor
  · rintro ⟨w,run⟩
    cases atIndex : after.equations[before.equations.length]? with
    | none => simp [checkProjection,atIndex] at run
    | some row =>
      have found : exactOrderedAppend before after row = true ∧
          (row.left = site ∧ checkEq before (.variable site) row.right w.equality = true) ∧
          checksNamedProjectionCut before site row.right w.cut = true := by
        simpa [checkProjection,atIndex,Bool.and_eq_true,and_assoc] using run
      rcases row with ⟨left,term⟩
      obtain ⟨append,⟨rfl,cert⟩,cut⟩ := found
      cases shape : shapeOf term with
      | none => simp [checksNamedProjectionCut,shape] at cut
      | some form =>
        obtain ⟨safe,never⟩ := (original_projection_cut_has_finite_wire_exactly_when_safe shape).mp ⟨w.cut,cut⟩
        exact ⟨term,form,(checks_single_ordered_extension_exactly ..).mp append,shape,
          (exact_finite_data_eq_check_iff_independent_Derives453 ..).mp ⟨w.equality,cert⟩,safe,never⟩
  · rintro ⟨term,form,rfl,shape,claims,safe,returns⟩
    obtain ⟨proof,eq⟩ := (exact_finite_data_eq_check_iff_independent_Derives453 ..).mpr claims
    obtain ⟨cut,passes⟩ := (original_projection_cut_has_finite_wire_exactly_when_safe shape).mpr ⟨safe,returns⟩
    have ix : (extendedRows before ⟨site,term⟩).equations[before.equations.length]? =
        some (⟨site,term⟩ : Equation) := by simp [extendedRows]
    exact ⟨⟨proof,cut⟩,by simp [checkProjection,ix,
      (checks_single_ordered_extension_exactly ..).mpr rfl,eq,passes]⟩

theorem exact_projection_keeps_models_in_both_directions {before after : RawState} {site : Nat}
    (h : ProjectionAt before after site) (m) :
    Models after m ↔ Models before m := by
  obtain ⟨term,_,rfl,_,proof,_,_⟩ := h
  constructor
  · intro fit
    exact ⟨fit.1,fun row found => fit.2 row (List.mem_append_left _ found)⟩
  · intro fit
    refine ⟨fit.1,?_⟩
    intro row found
    change row ∈ before.equations ++ [(⟨site,term⟩ : Equation)] at found
    rcases List.mem_append.mp found with old | new
    · exact fit.2 row old
    · obtain rfl := List.mem_singleton.mp new
      exact semantic proof m fit

theorem exact_projection_retains_old_raw_ordinals_and_the_actual_new_slot
    {before after : RawState} {site : Nat}
    (h : ProjectionAt before after site) :
    (∀ i < before.equations.length, after.equations[i]? = before.equations[i]?) ∧
    ∃ e : Equation, after.equations[before.equations.length]? = some e ∧ e.left = site := by
  obtain ⟨term,_,rfl,_,_,_,_⟩ := h
  constructor
  · intro i lt
    simp [extendedRows,List.getElem?_append_left lt]
  · refine ⟨⟨site,term⟩,?_,rfl⟩
    simp [extendedRows]

theorem exact_projection_keeps_all_raw_k2_sites {before after : RawState} {site : Nat}
    (h : ProjectionAt before after site) (atAny : Nat) :
    AliasCycle after (observed after) atAny ↔ AliasCycle before (observed before) atAny := by
  obtain ⟨term,_,rfl,shape,_,_,notReturn⟩ := h
  apply one_nonalias_raw_row_does_not_change_k2_under_original_class_no_return
  · intro n eq
    rw [eq] at shape
    cases shape
  · intro form parsed
    cases Option.some.inj (shape.symm.trans parsed)
    exact notReturn

end Yulang.GeneralDeclarativeI65.I72.NamedProjection464
