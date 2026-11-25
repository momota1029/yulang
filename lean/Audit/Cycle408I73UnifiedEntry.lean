import Yulang.GeneralDeclarativeI65I73UnifiedEntry408
import Yulang.GeneralDeclarativeWitnessCoverageFixture357
import Yulang.GeneralDeclarativeWitnessCycleFixture350

namespace Yulang.GeneralDeclarativeI65.I72.Checker408.Integration
open GeneralDeclarativeI65 (B6OccurrenceAtlas401)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessCoverageFixture357 (prepare)
open GeneralSourceMetadataBareBundle291 (InputBundle)

def leaf : Declaration := ⟨88,7,[],[],[],[]⟩

def source (withRole : Bool) : InputBundle :=
  ⟨⟨.absent,[]⟩,⟨.absent,[]⟩,⟨0,if withRole then [⟨7,0,[]⟩] else []⟩,[leaf]⟩

def problem (withRole : Bool) : Option Problem := do
  let metadata ← prepare (source withRole)
  let state : GeneralDeclarativeI65.State := ⟨⟨metadata,⟨⟨[],[]⟩,[]⟩,[]⟩,[],[],[]⟩
  let atlas : B6OccurrenceAtlas401 state := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨state,atlas⟩,⟨[27],⟨7,[],[]⟩⟩⟩

def oldFallbackProbe : Bool :=
  ((problem false).map fun p => Check408.check p (Check408.nullaryReport leaf) .nullary).getD false

def officialNullaryProbe (declared : Bool) : Bool :=
  ((problem declared).map fun p => check p (Check408.nullaryReport leaf) .nullary).getD false

def officialRawIndependentProbe : Bool :=
  ((problem false).map fun pr =>
    let original := {pr.state.core with current :=
      {pr.state.core.current with ordinary := GeneralDeclarativeWitnessCycleFixture350.state}}
    let atlas : B6OccurrenceAtlas401 original := ⟨fun _ _ _ _ => none⟩
    let root := {pr.root with demand := GeneralDeclarativeWitnessCycleFixture350.d}
    check ⟨⟨original,atlas⟩,root⟩ Check408.rawReport
      (.rawRoot GeneralDeclarativeWitnessCycleFixture350.certificate)).getD false

/-- Same state and declaration shape, with only the authored role row
removed. A fallback used to pass structural arity checks; the public
checker now validates the declaration instead. -/
theorem arity_fallback_is_not_authoritative408 :
    oldFallbackProbe = true ∧ officialNullaryProbe false = false := by
  decide +kernel

theorem authored_nullary_passes_official_check408 :
    officialNullaryProbe true = true := by
  decide +kernel

theorem actual_raw_k2_is_not_blocked_by_missing_role_table408 :
    officialRawIndependentProbe = true := by
  decide +kernel

def witnessModel : I72.Model := ⟨fun _ => (.base .int,Common.rowEmpty),fun _ => none,fun _ => none⟩

theorem official_checked_leaf_is_nonvacuous408 :
    ∃ p, problem true = some p ∧
      check p (Check408.nullaryReport leaf) .nullary = true ∧
      I72.Fits p.state witnessModel ∧
      I72.DictionaryEvidence p.state witnessModel p.root (.node leaf.id []) := by
  have tested := authored_nullary_passes_official_check408
  unfold officialNullaryProbe at tested
  cases sourceAt : problem true with
  | none => simp [sourceAt] at tested
  | some p =>
    have accepted : check p (Check408.nullaryReport leaf) .nullary = true := by
      simpa [sourceAt] using tested
    have fit : I72.Fits p.state witnessModel := by
      unfold problem at sourceAt
      cases exact : prepare (source true) with
      | none => simp [exact] at sourceAt
      | some _ =>
        simp only [exact,Option.pure_def] at sourceAt
        cases sourceAt
        refine ⟨⟨⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩,?_⟩,?_⟩ <;>
          intro _ empty <;> cases empty
    exact ⟨p,rfl,accepted,fit,Check408.accepted_selected_dictionary_in_every_model408
      p (Check408.nullaryReport leaf) .nullary (accepted_implies_branch_engine408 p _ _ accepted)
      _ rfl witnessModel fit⟩

#print axioms arity_fallback_is_not_authoritative408
#print axioms authored_nullary_passes_official_check408
#print axioms actual_raw_k2_is_not_blocked_by_missing_role_table408
#print axioms official_checked_leaf_is_nonvacuous408

end Yulang.GeneralDeclarativeI65.I72.Checker408.Integration
