import Yulang.GeneralDeclarativeI65I74RecordEntry412

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordK2412
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeK2Alias321 (cycle_alias)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeInspect321 (Visit PatternK2)
open GeneralDeclarativeGraphRows321 (observed structural)
open CommonRoleOutermostResolver (Tree Summarizes)
open Checker408 (Problem Result)

theorem actual_entered_site_is_not_even_a_root_alias412 {p : Problem} (snap : VerifiedField p) :
    ¬GeneralDeclarativeLowerKnown321.Alias p.state.core.current.ordinary snap.rejection.field.input.lower snap.rejection.field.site := by
  intro aliased
  apply snap.rootSafe
  refine ⟨snap.rejection.field.input,by simp [snap.rejection.field.asked],?_⟩
  exact cycle_alias aliased snap.rejection.cycle

theorem checked_field_retains_exact_head_origin_and_raw_site412
    (p : Problem) (r : Result) (w : FieldWire) (yes : check p r (.fieldCycle w) = true) :
    ∃ (d : Declaration) (a : ActualRecordField p.state p.root d),
      d ∈ visible p.state.core p.root ∧
      Visit (structural p.state.core.current.ordinary) a.input.lower
        (query412 a.box a.tick a.binder) a.site ∧
      PatternK2 p.state.core.current.ordinary a.input.lower (query412 a.box a.tick a.binder) ∧
      a.site ≠ a.input.lower ∧ ¬RootCycle p.state p.root ∧
      r = Check408.rawReport := by
  obtain ⟨d,scope,v,_,result⟩ := checked_field_reflects_actual_original_rejection412 p r w yes
  let a := v.rejection.field
  refine ⟨v.rejection.decl,a,by simp [a.only],actual_record_field_is_entered412 a,
    actual_record_field_K2_on_unfiltered_graph412 a v.rejection.cycle,?_,v.rootSafe,result⟩
  intro same
  apply actual_entered_site_is_not_even_a_root_alias412 v
  change GeneralDeclarativeLowerKnown321.Alias p.state.core.current.ordinary a.input.lower a.site
  rw [same]
  exact alias_refl _

private theorem same_visible_row412 {s q d e} (a : ActualRecordField s q d)
    (old : e ∈ visible s.core q) : e = d := by
  rw [a.only] at old
  exact List.mem_singleton.mp old

private theorem singleton_no_ambiguity412 {s q d} (a : ActualRecordField s q d)
    (count : 2 ≤ (visible s.core q).length) : False := by
  simp [a.only] at count

private theorem record_never_normalizes_to_app412 {s q d e}
    (a : ActualRecordField s q d) (seen : e ∈ visible s.core q)
    {p : Pattern} (written : e.head = [p]) {k args} (normal : normalize p = .app k args) : False := by
  cases same_visible_row412 a seen
  have same := (List.cons.inj (written.symm.trans a.head)).1
  rw [same] at normal
  change Pattern.record a.box _ _ = Pattern.app k args at normal
  cases normal

private theorem no_repeated_other412 {s q d v} (a : ActualRecordField s q d)
    (old : RepeatedOther403 s q v) : False := by
  cases old with
  | ambiguous _ count => exact singleton_no_ambiguity412 a count

private theorem no_authored_other412 {s q d v needs} (a : ActualRecordField s q d)
    (old : variableWithNativeK2403.other s q v needs) : False := by
  rcases old.2 with ambiguous|⟨_,_,enter,_⟩
  · exact no_repeated_other412 a ambiguous
  · exact record_never_normalizes_to_app412 a enter.visibleRow enter.exactHead enter.dispatch

private theorem no_completed_other412 {s q d v needs} (a : ActualRecordField s q d)
    (old : completedNativePrioritySource404.other s q v needs) : False := by
  rcases old with regular|⟨_,⟨visit⟩⟩
  · exact no_authored_other412 a regular
  · exact record_never_normalizes_to_app412 a visit.entry.visibleRow visit.entry.exactHead visit.entry.dispatch

private theorem no_completed_choice_other412 {s q d v needs} (a : ActualRecordField s q d)
    (old : completedChoiceSource404.other s q v needs) : False := by
  rcases old with regular|⟨_,⟨ambiguous⟩⟩
  · exact no_completed_other412 a regular
  · exact singleton_no_ambiguity412 a ambiguous.two

theorem no_prior_candidate_diagnostic_for_X10_412 {s q d v needs} (a : ActualRecordField s q d) :
    ¬WhereCycle411.R3.other s q v needs := by
  rintro ⟨rule,family,old⟩
  cases family with
  | variableOnly =>
    cases old.2 with
    | ambiguous _ count => exact singleton_no_ambiguity412 a count
  | repeated | whereTree => exact no_repeated_other412 a old.2
  | nativeK2 | supported => exact no_authored_other412 a old
  | supportedK2 => exact no_completed_other412 a old
  | supportedAmbiguity | authoredNative => exact no_completed_choice_other412 a old

theorem no_prior_election_for_X10_412 {s q d}
    (a : ActualRecordField s q d) (e : Event s q) {needs} :
    ¬WhereCycle411.R3.elected s q e needs := by
  have owner := same_visible_row412 a e.frame.inScope
  have pattern : closedHead412 a.box a.tick a.empty a.binder ∈ d.head := by simp [a.head]
  rintro ((legacy|old)|that)
  · rcases legacy with r0|named
    · rcases R0_selection_uses_independent_original_rule407 e r0 with general|native
      · obtain ⟨_,bad,_⟩ := general.2 d (by simp [a.only]) _ pattern
        cases bad
      · obtain ⟨n⟩ := native
        have h := (List.cons.inj (n.test.writtenHead.symm.trans
          ((congrArg Declaration.head owner).trans a.head))).1
        cases h
    · obtain ⟨_,⟨point⟩⟩ := named
      have h := (List.cons.inj (point.test.named.symm.trans
        ((congrArg Declaration.head owner).trans a.head))).1
      cases h
  · obtain ⟨_,⟨leaf⟩⟩ := old
    have h := (List.cons.inj (leaf.test.named.symm.trans
      ((congrArg Declaration.head owner).trans a.head))).1
    cases h
  · obtain ⟨_,⟨whereList⟩⟩ := that
    have h := (List.cons.inj (whereList.test.named.symm.trans
      ((congrArg Declaration.head owner).trans a.head))).1
    cases h

theorem every_X10_trace_is_record_head_rejection412 {p : Problem} (snap : VerifiedField p)
    {t e} (trace : SourceTrace R4 p.state p.root t e) :
    t = .rejected ∧ e = none := by
  cases trace with
  | rootK2 root => exact (snap.rootSafe root).elim
  | selected event _ older _ _ =>
    exact (no_prior_election_for_X10_412 snap.rejection.field event older).elim
  | other v _ law _ =>
    rcases law with prior|⟨_,rfl,_⟩
    · exact (no_prior_candidate_diagnostic_for_X10_412 snap.rejection.field prior).elim
    · exact ⟨rfl,rfl⟩

theorem field_and_previous_cannot_both_check412 (p : Problem) (r other : Result)
    (w : FieldWire) (old : WhereCycle411.Witness) (yes : check p r (.fieldCycle w) = true) :
    check p other (.previous old) = false := by
  obtain ⟨_,_,packet,_,_⟩ := checked_field_reflects_actual_original_rejection412 p r w yes
  cases prior : check p other (.previous old) with
  | false => rfl
  | true =>
    have before : WhereCycle411.check p other old = true := prior
    obtain ⟨e,t,_,_⟩ := (WhereCycle411.check_sound p other old before).1
    generalize other.tree = tree at t
    cases t with
    | rootK2 root => exact (packet.rootSafe root).elim
    | other _ _ rule _ =>
      exact (no_prior_candidate_diagnostic_for_X10_412 packet.rejection.field rule).elim
    | selected event _ rule _ _ =>
      exact (no_prior_election_for_X10_412 packet.rejection.field event rule).elim

theorem checked_results_are_unique412 (p : Problem) (r other : Result) (x y : Witness)
    (first : check p r x = true) (second : check p other y = true) : r = other := by
  cases x with
  | unsupported => simp [check] at first
  | previous old =>
    cases y with
    | unsupported => simp [check] at second
    | previous prior => exact WhereCycle411.checked_results_are_unique411 p r other old prior first second
    | fieldCycle data =>
      rw [field_and_previous_cannot_both_check412 p other r data old second] at first
      cases first
  | fieldCycle data =>
    cases y with
    | unsupported => simp [check] at second
    | previous prior =>
      rw [field_and_previous_cannot_both_check412 p r other data prior first] at second
      cases second
    | fieldCycle another =>
      obtain ⟨_,_,_,_,a⟩ := checked_field_reflects_actual_original_rejection412 p r data first
      obtain ⟨_,_,_,_,b⟩ := checked_field_reflects_actual_original_rejection412 p other another second
      exact a.trans b.symm

end Yulang.GeneralDeclarativeI65.I72.RecordK2412
