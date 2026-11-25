import Yulang.GeneralDeclarativeI65I74OpenTailEntry414

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.OpenTail414
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)
open CommonRoleOutermostResolver (Tree Summarizes)
open Checker408 (Problem Result)
open RecordK2412 (closedWhere412 closedHead412 query412)

private theorem record_head414 {s q} (a : OpenTailPending s q)
    (d : Declaration) (h : d ∈ visible s.core q) :
    ∃ l p t, d.head = [.record l p t] := by
  rw [a.candidate.exactVisible] at h
  cases List.mem_singleton.mp h
  exact ⟨_,_,_,a.candidate.head⟩

private theorem any_record_rules_out_all_var414 {s q} (shape : OpenTailPending s q)
    (assumed : (d : Declaration) → d ∈ visible s.core q → RepeatedRow403 q d) : False := by
  let d := shape.candidate.decl
  have member : d ∈ visible s.core q := by simp [shape.candidate.exactVisible,d]
  obtain ⟨label,p,tail,h⟩ := record_head414 shape d member
  have visiblePattern : Pattern.record label p tail ∈ d.head := by simp [h]
  rw [(assumed d member).literal] at visiblePattern
  obtain ⟨_,_,bad⟩ := List.mem_map.mp visiblePattern
  cases bad

private theorem no_app_from_record414 {s q} (scan : OpenTailPending s q)
    {d : Declaration} (seen : d ∈ visible s.core q)
    {p : Pattern} (written : d.head = [p]) {k args}
    (normal : normalize p = .app k args) : False := by
  obtain ⟨label,payload,tail,head⟩ := record_head414 scan d seen
  have same := (List.cons.inj (written.symm.trans head)).1
  rw [same] at normal
  change Pattern.record label _ _ = Pattern.app k args at normal
  cases normal

private theorem no_repeated_other414 {s q v} (shape : OpenTailPending s q)
    (old : RepeatedOther403 s q v) : False := by
  cases old with
  | ambiguous scope _ =>
    obtain ⟨s⟩ := scope
    exact any_record_rules_out_all_var414 shape s.allVisible

private theorem no_native_other414 {s q v needs} (shape : OpenTailPending s q)
    (old : variableWithNativeK2403.other s q v needs) : False := by
  rcases old.2 with repeatCase|⟨_,_,opened,_⟩
  · exact no_repeated_other414 shape repeatCase
  · exact no_app_from_record414 shape opened.visibleRow opened.exactHead opened.dispatch

private theorem no_completed_native_other414 {s q v needs} (shape : OpenTailPending s q)
    (old : completedNativePrioritySource404.other s q v needs) : False := by
  rcases old with earlier|⟨_,⟨opened⟩⟩
  · exact no_native_other414 shape earlier
  · exact no_app_from_record414 shape opened.entry.visibleRow opened.entry.exactHead opened.entry.dispatch

private theorem no_completed_choice_other414 {s q v needs} (shape : OpenTailPending s q)
    (old : completedChoiceSource404.other s q v needs) : False := by
  rcases old with earlier|⟨_,⟨scope⟩⟩
  · exact no_completed_native_other414 shape earlier
  · exact any_record_rules_out_all_var414 shape scope.allVisible

theorem no_R4_diagnostic_on_open_tail414 {s q v needs} (shape : OpenTailPending s q) :
    ¬RecordK2412.R4.other s q v needs := by
  rintro (⟨_,family,old⟩|⟨_,_,⟨one⟩⟩)
  · cases family with
    | variableOnly =>
      cases old.2 with
      | ambiguous scope _ =>
        obtain ⟨someScope⟩ := scope
        let d := shape.candidate.decl
        have member : d ∈ visible s.core q := by simp [shape.candidate.exactVisible,d]
        obtain ⟨l,p,t,head⟩ := record_head414 shape d member
        have literal : Pattern.record l p t ∈ d.head := by simp [head]
        let mine := someScope.allVisible d member
        rw [mine.literal] at literal
        obtain ⟨_,_,absurd⟩ := List.mem_map.mp literal
        cases absurd
    | repeated | whereTree => exact no_repeated_other414 shape old.2
    | nativeK2 | supported => exact no_native_other414 shape old
    | supportedK2 => exact no_completed_native_other414 shape old
    | supportedAmbiguity | authoredNative => exact no_completed_choice_other414 shape old
  · have oneDecl : one.decl ∈ visible s.core q := by simp [one.field.only]
    have eq : one.decl = shape.candidate.decl := by
      simpa [shape.candidate.exactVisible] using oneDecl
    have closed := shape.candidate.head.symm.trans ((congrArg Declaration.head eq).symm.trans one.field.head)
    simp [openHead,closedHead412] at closed

theorem no_R4_election_on_open_tail414 {s q needs} (shape : OpenTailPending s q)
    (e : Event s q) : ¬RecordK2412.R4.elected s q e needs := by
  obtain ⟨label,payload,tail,head⟩ := record_head414 shape e.frame.decl e.frame.inScope
  have written : Pattern.record label payload tail ∈ e.frame.decl.head := by simp [head]
  rintro (((legacy|named)|leaf)|whereList)
  · rcases R0_selection_uses_independent_original_rule407 e legacy with plain|native
    · obtain ⟨_,bad,_⟩ := plain.2 e.frame.decl e.frame.inScope _ written
      cases bad
    · obtain ⟨source⟩ := native
      have bad := (List.cons.inj (source.test.writtenHead.symm.trans head)).1
      cases bad
  · obtain ⟨_,⟨name⟩⟩ := named
    exact no_app_from_record414 shape e.frame.inScope name.test.named rfl
  · obtain ⟨_,⟨list⟩⟩ := leaf
    exact no_app_from_record414 shape e.frame.inScope list.test.named rfl
  · obtain ⟨_,⟨list⟩⟩ := whereList
    exact no_app_from_record414 shape e.frame.inScope list.test.named rfl

theorem no_R5_diagnostic_on_open_tail414 {s q v needs} (a : OpenTailPending s q) :
    ¬ MixedRecord413.R5.other s q v needs := by
  rintro (old|fresh)
  · exact no_R4_diagnostic_on_open_tail414 a old
  · obtain ⟨_,_,⟨data⟩⟩ := fresh
    have h := data.rivalsExist
    simp [a.candidate.exactVisible] at h

theorem actual_open_tail_waits_in_every_R6_trace414 {p : Problem} (scan : OpenVerified p)
    {t e} (trace : SourceTrace R6 p.state p.root t e) : t = .pending ∧ e = none := by
  cases trace with
  | rootK2 cyclic => exact False.elim (scan.rootSafe cyclic)
  | selected event _ prior _ _ => exact False.elim (no_R4_election_on_open_tail414 scan.pending event prior)
  | other v _ rule _ =>
    rcases rule with before|⟨_,rfl,_⟩
    · exact False.elim (no_R5_diagnostic_on_open_tail414 scan.pending before)
    · exact ⟨rfl,rfl⟩

theorem prior_checker_remains_disjoint414 (p : Problem) (r a : Result) (w : OpenWire)
    (old : MixedRecord413.Witness) (yes : check p r (.openTail w) = true) : check p a (.previous old) = false := by
  obtain ⟨scan,_,_⟩ := checked_open_tail_reflects_original414 p r w yes
  cases previous : check p a (.previous old) with
  | false => rfl
  | true =>
    exfalso
    have before : MixedRecord413.check p a old = true := previous
    obtain ⟨e,t,_,_⟩ := (MixedRecord413.check_sound p a old before).1
    generalize a.tree = tree at t
    cases t with
    | rootK2 cyclic => exact scan.rootSafe cyclic
    | selected event _ prior _ _ => exact no_R4_election_on_open_tail414 scan.pending event prior
    | other _ _ prior _ => exact no_R5_diagnostic_on_open_tail414 scan.pending prior

theorem checked_results_are_unique414 (p : Problem) (r a : Result) (u v : Witness)
    (first : check p r u = true) (second : check p a v = true) : r = a := by
  cases u with
  | unsupported => simp [check] at first
  | previous old =>
    cases v with
    | unsupported => simp [check] at second
    | previous other => exact MixedRecord413.checked_results_are_unique413 p r a old other first second
    | openTail data =>
      rw [prior_checker_remains_disjoint414 p a r data old second] at first
      cases first
  | openTail data =>
    cases v with
    | unsupported => simp [check] at second
    | previous other =>
      rw [prior_checker_remains_disjoint414 p r a data other first] at second
      cases second
    | openTail another =>
      obtain ⟨_,_,r0⟩ := checked_open_tail_reflects_original414 p r data first
      obtain ⟨_,_,a0⟩ := checked_open_tail_reflects_original414 p a another second
      exact r0.trans a0.symm

end Yulang.GeneralDeclarativeI65.I72.OpenTail414
