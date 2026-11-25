import Yulang.GeneralDeclarativeI65I74MixedRecordRival413

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.MixedRecord413
open GeneralDeclarativeI65
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeK2Alias321 (cycle_alias)
open RecordK2412 (recordInput412 closedHead412 closedWhere412)
open Checker408 (Problem Result)

theorem open_field_is_not_a_parent_alias413 {p : Problem} (v : MixedVerified p) :
    ¬GeneralDeclarativeLowerKnown321.Alias p.state.core.current.ordinary
      v.rejection.outer.root v.rejection.outer.site := by
  intro same
  apply v.rootSafe
  refine ⟨point v.rejection.outer.root,by simp [v.rejection.outer.args],?_⟩
  exact cycle_alias same v.rejection.actualCycle

theorem same_visible_list_has_same_opening_ordinal413 {s q}
    (a b : MixedRecordRejection s q) : a.tape.opening.ordinal = b.tape.opening.ordinal := by
  by_cases different : a.tape.opening.ordinal = b.tape.opening.ordinal
  · exact different
  exfalso
  let openRow := a.tape.opening
  obtain ⟨plain⟩ := b.tape.actual_rival openRow.ordinal openRow.fromOriginalList different
  have incompatible := (List.cons.inj (openRow.source.head.symm.trans plain.head)).1
  change closedHead412 a.outer.box openRow.source.nextField openRow.source.empty openRow.source.binder =
    closedWhere412 b.outer.box plain.empty plain.binder at incompatible
  have clash := (Pattern.record.inj incompatible).2.1
  cases clash

theorem same_argument_point_forces_exact_same_site413 {s q}
    (a b : ActualOuterRecord s q) (m : I72.Model) (fit : Fits s m) :
    a.root = b.root ∧ a.box = b.box ∧ a.site = b.site := by
  have r : a.root = b.root := by
    have arguments := (List.cons.inj (a.args.symm.trans b.args)).1
    exact congrArg GeneralDeclarativeWhere319.Capture.lower arguments
  have left := fit.2 _ a.actualOrigin
  have right := fit.2 _ b.actualOrigin
  rw [a.originalSlot,r,a.originalTerm] at left
  rw [b.originalSlot,b.originalTerm] at right
  have same := Option.some.inj (left.symm.trans right)
  change recordInput412 a.box a.site = recordInput412 b.box b.site at same
  injection same with term
  exact ⟨r,(Core.PresenceGeneration.TyTerm.record.inj term).1,
    Core.PresenceGeneration.TyTerm.var.inj (Core.PresenceGeneration.TyTerm.record.inj term).2.1⟩

theorem fixed_input_and_fitting_model_force_same_location413 {p : Problem}
    (a b : MixedVerified p) (m : I72.Model) (fit : Fits p.state m) :
    a.location = b.location := by
  have ix := same_visible_list_has_same_opening_ordinal413 a.rejection b.rejection
  obtain ⟨root,box,site⟩ := same_argument_point_forces_exact_same_site413 a.rejection.outer b.rejection.outer m fit
  have old := a.rejection.tape.opening.fromOriginalList
  rw [ix] at old
  have d := Option.some.inj (old.symm.trans b.rejection.tape.opening.fromOriginalList)
  simp [MixedVerified.location,ix,root,box,site,d]

theorem same_input_two_checked_witnesses_cannot_reassign_location413
    (p : Problem) (r t : Result) (w u : MixedWire)
    (m : I72.Model) (fit : Fits p.state m)
    {first second : MixedLocation}
    (one : locate p r w = some first) (two : locate p t u = some second) :
    first = second := by
  obtain ⟨a,atA,_,_,_,_,_⟩ := checked_location_is_original_candidate_and_visit413 p r w one
  obtain ⟨b,atB,_,_,_,_,_⟩ := checked_location_is_original_candidate_and_visit413 p t u two
  exact atA.symm.trans ((fixed_input_and_fitting_model_force_same_location413 a b m fit).trans atB)

end Yulang.GeneralDeclarativeI65.I72.MixedRecord413
