import Yulang.GeneralDeclarativeI65I74MixedRecordEntry413

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.MixedRecord413
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)
open CommonRoleOutermostResolver (Tree Summarizes)
open Checker408 (Problem Result)
open RecordK2412 (closedWhere412 closedHead412 query412)

def RecordHead413 (row : Declaration) : Prop :=
  ∃ label payload tail, row.head = [.record label payload tail]

theorem PlainTape.record_head {s q} {outer : ActualOuterRecord s q} {rows} (t : PlainTape outer rows)
    (d : Declaration) (here : d ∈ rows) : RecordHead413 d := by
  induction t with
  | nil => cases here
  | cons hd _ ih =>
    rcases List.mem_cons.mp here with atFront|later
    · cases atFront
      exact ⟨_,_,_,hd.head⟩
    · exact ih later

theorem MixedTape.record_head {s q} {outer : ActualOuterRecord s q} {rows} (t : MixedTape outer rows)
    (d : Declaration) (here : d ∈ rows) : RecordHead413 d := by
  induction t with
  | opens hd rest =>
    rcases List.mem_cons.mp here with atFront|later
    · cases atFront
      exact ⟨_,_,_,hd.head⟩
    · exact rest.record_head _ later
  | next hd _ ih =>
    rcases List.mem_cons.mp here with atFront|later
    · cases atFront
      exact ⟨_,_,_,hd.head⟩
    · exact ih later

private theorem any_record_rules_out_all_var413 {s q} (shape : MixedRecordRejection s q)
    (assumed : (d : Declaration) → d ∈ visible s.core q → RepeatedRow403 q d) : False := by
  let d := shape.tape.opening.decl
  have member : d ∈ visible s.core q := List.mem_of_getElem? shape.tape.opening.fromOriginalList
  obtain ⟨label,p,tail,h⟩ := shape.tape.record_head d member
  have visiblePattern : Pattern.record label p tail ∈ d.head := by simp [h]
  rw [(assumed d member).literal] at visiblePattern
  obtain ⟨_,_,bad⟩ := List.mem_map.mp visiblePattern
  cases bad

private theorem no_app_from_record413 {s q} (scan : MixedRecordRejection s q)
    {d : Declaration} (seen : d ∈ visible s.core q)
    {p : Pattern} (written : d.head = [p]) {k args}
    (normal : normalize p = .app k args) : False := by
  obtain ⟨label,payload,tail,head⟩ := scan.tape.record_head d seen
  have same := (List.cons.inj (written.symm.trans head)).1
  rw [same] at normal
  change Pattern.record label _ _ = Pattern.app k args at normal
  cases normal

private theorem no_repeated_other413 {s q v} (shape : MixedRecordRejection s q)
    (old : RepeatedOther403 s q v) : False := by
  cases old with
  | ambiguous scope _ =>
    obtain ⟨s⟩ := scope
    exact any_record_rules_out_all_var413 shape s.allVisible

private theorem no_native_other413 {s q v needs} (shape : MixedRecordRejection s q)
    (old : variableWithNativeK2403.other s q v needs) : False := by
  rcases old.2 with repeatCase|⟨_,_,opened,_⟩
  · exact no_repeated_other413 shape repeatCase
  · exact no_app_from_record413 shape opened.visibleRow opened.exactHead opened.dispatch

private theorem no_completed_native_other413 {s q v needs} (shape : MixedRecordRejection s q)
    (old : completedNativePrioritySource404.other s q v needs) : False := by
  rcases old with earlier|⟨_,⟨opened⟩⟩
  · exact no_native_other413 shape earlier
  · exact no_app_from_record413 shape opened.entry.visibleRow opened.entry.exactHead opened.entry.dispatch

private theorem no_completed_choice_other413 {s q v needs} (shape : MixedRecordRejection s q)
    (old : completedChoiceSource404.other s q v needs) : False := by
  rcases old with earlier|⟨_,⟨scope⟩⟩
  · exact no_completed_native_other413 shape earlier
  · exact any_record_rules_out_all_var413 shape scope.allVisible

theorem no_prior_diagnostic_on_mixed_record413 {s q v needs} (shape : MixedRecordRejection s q) :
    ¬RecordK2412.R4.other s q v needs := by
  rintro (⟨_,family,old⟩|⟨_,_,⟨one⟩⟩)
  · cases family with
    | variableOnly =>
      cases old.2 with
      | ambiguous scope _ =>
        obtain ⟨someScope⟩ := scope
        let d := shape.tape.opening.decl
        have member : d ∈ visible s.core q := List.mem_of_getElem? shape.tape.opening.fromOriginalList
        obtain ⟨l,p,t,head⟩ := shape.tape.record_head d member
        have literal : Pattern.record l p t ∈ d.head := by simp [head]
        let mine := someScope.allVisible d member
        rw [mine.literal] at literal
        obtain ⟨_,_,absurd⟩ := List.mem_map.mp literal
        cases absurd
    | repeated | whereTree => exact no_repeated_other413 shape old.2
    | nativeK2 | supported => exact no_native_other413 shape old
    | supportedK2 => exact no_completed_native_other413 shape old
    | supportedAmbiguity | authoredNative => exact no_completed_choice_other413 shape old
  · have atLeast := shape.rivalsExist
    simp [one.field.only] at atLeast

theorem no_prior_election_on_mixed_record413 {s q needs} (shape : MixedRecordRejection s q)
    (e : Event s q) : ¬RecordK2412.R4.elected s q e needs := by
  obtain ⟨label,payload,tail,head⟩ := shape.tape.record_head e.frame.decl e.frame.inScope
  have written : Pattern.record label payload tail ∈ e.frame.decl.head := by simp [head]
  rintro (((legacy|named)|leaf)|whereList)
  · rcases R0_selection_uses_independent_original_rule407 e legacy with plain|native
    · obtain ⟨_,bad,_⟩ := plain.2 e.frame.decl e.frame.inScope _ written
      cases bad
    · obtain ⟨source⟩ := native
      have bad := (List.cons.inj (source.test.writtenHead.symm.trans head)).1
      cases bad
  · obtain ⟨_,⟨name⟩⟩ := named
    exact no_app_from_record413 shape e.frame.inScope name.test.named rfl
  · obtain ⟨_,⟨list⟩⟩ := leaf
    exact no_app_from_record413 shape e.frame.inScope list.test.named rfl
  · obtain ⟨_,⟨list⟩⟩ := whereList
    exact no_app_from_record413 shape e.frame.inScope list.test.named rfl

theorem actual_nested_K2_has_priority_over_every_R5_trace413 {p : Problem} (scan : MixedVerified p)
    {t e} (trace : SourceTrace R5 p.state p.root t e) : t = .rejected ∧ e = none := by
  cases trace with
  | rootK2 cyclic => exact False.elim (scan.rootSafe cyclic)
  | selected event _ prior _ _ => exact False.elim (no_prior_election_on_mixed_record413 scan.rejection event prior)
  | other v _ rule _ =>
    rcases rule with before|⟨_,rfl,_⟩
    · exact False.elim (no_prior_diagnostic_on_mixed_record413 scan.rejection before)
    · exact ⟨rfl,rfl⟩

theorem prior_checker_remains_disjoint413 (p : Problem) (r a : Result) (w : MixedWire)
    (old : RecordK2412.Witness) (yes : check p r (.mixedHead w) = true) : check p a (.previous old) = false := by
  obtain ⟨scan,_,_⟩ := checked_mixed_head_reflects_original413 p r w yes
  cases previous : check p a (.previous old) with
  | false => rfl
  | true =>
    exfalso
    have before : RecordK2412.check p a old = true := previous
    obtain ⟨e,t,_,_⟩ := (RecordK2412.check_sound p a old before).1
    generalize a.tree = tree at t
    cases t with
    | rootK2 cyclic => exact scan.rootSafe cyclic
    | selected event _ prior _ _ => exact no_prior_election_on_mixed_record413 scan.rejection event prior
    | other _ _ prior _ => exact no_prior_diagnostic_on_mixed_record413 scan.rejection prior

theorem checked_results_are_unique413 (p : Problem) (r a : Result) (u v : Witness)
    (first : check p r u = true) (second : check p a v = true) : r = a := by
  cases u with
  | unsupported => simp [check] at first
  | previous old =>
    cases v with
    | unsupported => simp [check] at second
    | previous other => exact RecordK2412.checked_results_are_unique412 p r a old other first second
    | mixedHead data =>
      rw [prior_checker_remains_disjoint413 p a r data old second] at first
      cases first
  | mixedHead data =>
    cases v with
    | unsupported => simp [check] at second
    | previous other =>
      rw [prior_checker_remains_disjoint413 p r a data other first] at second
      cases second
    | mixedHead another =>
      obtain ⟨_,_,r0⟩ := checked_mixed_head_reflects_original413 p r data first
      obtain ⟨_,_,a0⟩ := checked_mixed_head_reflects_original413 p a another second
      exact r0.trans a0.symm

end Yulang.GeneralDeclarativeI65.I72.MixedRecord413
