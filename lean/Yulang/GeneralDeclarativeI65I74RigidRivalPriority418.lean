import Yulang.GeneralDeclarativeI65I74RigidRivalEntry418
import Yulang.GeneralDeclarativeI65I74X6AmbiguousPriority417
import Yulang.GeneralDeclarativeI65I74PlainMergedPriority416

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RigidRival418
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)
open Checker408 (Problem Result)
open RecordK2412 (closedHead412)

open PlainMerged416 (sourceX6 two_literal_plain_arms_normalize_to_one_actual_tag416)

theorem every_visible_candidate_is_a_variant_after_normalization418 {s q}
    (a : Winner s q) {d : Declaration} (seen : d ∈ visible s.core q) :
    ∃ p out, d.head = [p] ∧ normalize p = .variant a.rows.tag out := by
  rcases (actual_candidates_and_no_others418 a d).mp seen with rfl|rfl
  · exact ⟨_,_,a.winner.head,two_literal_plain_arms_normalize_to_one_actual_tag416 _ _ _ a.winner.unlike⟩
  · exact ⟨_,_,a.mismatch.rival.literal,rfl⟩

private theorem no_variable_scope418 {s q} (a : Winner s q)
    (scope : (d : Declaration) → d ∈ visible s.core q → RepeatedRow403 q d) : False := by
  let d := a.winner.candidate.decl
  have wrote : sourceX6 a.rows.tag a.winner.first a.winner.second ∈ d.head := by simp [d,a.winner.head]
  rw [(scope d a.winner.candidate.found).literal] at wrote
  obtain ⟨_,_,contradiction⟩ := List.mem_map.mp wrote
  cases contradiction

private theorem no_application_scope418 {s q} (a : Winner s q)
    {d : Declaration} (seen : d ∈ visible s.core q) {p : Pattern} (written : d.head = [p])
    {key args} (shape : normalize p = .app key args) : False := by
  obtain ⟨w,n,exactHead,normalized⟩ := every_visible_candidate_is_a_variant_after_normalization418 a seen
  have same := (List.cons.inj (written.symm.trans exactHead)).1
  rw [same,normalized] at shape
  cases shape

private theorem no_record_scope418 {s q} (a : Winner s q)
    {d : Declaration} (seen : d ∈ visible s.core q) {k payload tail}
    (head : d.head = [.record k payload tail]) : False := by
  obtain ⟨p,out,exactHead,normalized⟩ := every_visible_candidate_is_a_variant_after_normalization418 a seen
  have same := (List.cons.inj (exactHead.symm.trans head)).1
  rw [same] at normalized
  change .record k _ _ = Pattern.variant a.rows.tag out at normalized
  cases normalized

private theorem no_singleton_scope418 {s q} (a : Winner s q) (d : Declaration)
    (single : visible s.core q = [d]) : False := by
  have count := congrArg List.length single
  rcases a.ordered with h|h <;> simp [h] at count

private theorem no_repeat_other418 {s q v} (a : Winner s q)
    (old : RepeatedOther403 s q v) : False := by
  cases old with
  | ambiguous scope _ =>
    obtain ⟨s⟩ := scope
    exact no_variable_scope418 a s.allVisible

private theorem no_native_other418 {s q v needs} (a : Winner s q)
    (old : variableWithNativeK2403.other s q v needs) : False := by
  rcases old.2 with repeats|⟨_,_,view,_⟩
  · exact no_repeat_other418 a repeats
  · exact no_application_scope418 a view.visibleRow view.exactHead view.dispatch

private theorem no_closed_native_other418 {s q v needs} (a : Winner s q)
    (old : completedNativePrioritySource404.other s q v needs) : False := by
  rcases old with earlier|⟨_,⟨caller⟩⟩
  · exact no_native_other418 a earlier
  · exact no_application_scope418 a caller.entry.visibleRow caller.entry.exactHead caller.entry.dispatch

private theorem no_prior_choice_other418 {s q v needs} (a : Winner s q)
    (old : completedChoiceSource404.other s q v needs) : False := by
  rcases old with earlier|⟨_,⟨scope⟩⟩
  · exact no_closed_native_other418 a earlier
  · exact no_variable_scope418 a scope.allVisible

theorem no_old_diagnostic_on_rigid_rival418 {s q verdict needs}
    (a : Winner s q) : ¬ PlainMerged416.R8.other s q verdict needs := by
  rintro (((⟨_,family,old⟩|⟨_,_,⟨single⟩⟩)|mixed)|opened)
  · cases family with
    | variableOnly =>
      cases old.2 with
      | ambiguous scope _ =>
        obtain ⟨declared⟩ := scope
        let d := a.winner.candidate.decl
        have wrote : sourceX6 a.rows.tag a.winner.first a.winner.second ∈ d.head :=
          by simp [d,a.winner.head]
        rw [(declared.allVisible d a.winner.candidate.found).literal] at wrote
        obtain ⟨_,_,contradiction⟩ := List.mem_map.mp wrote
        cases contradiction
    | repeated | whereTree => exact no_repeat_other418 a old.2
    | nativeK2 | supported => exact no_native_other418 a old
    | supportedK2 => exact no_closed_native_other418 a old
    | supportedAmbiguity | authoredNative => exact no_prior_choice_other418 a old
  · exact no_singleton_scope418 a _ single.field.only
  · obtain ⟨_,_,⟨view⟩⟩ := mixed
    let d := view.tape.opening.decl
    have seen : d ∈ visible s.core q := List.mem_of_getElem? view.tape.opening.fromOriginalList
    obtain ⟨_,_,_,h⟩ := view.tape.record_head d seen
    exact no_record_scope418 a seen h
  · obtain ⟨_,_,⟨scope⟩⟩ := opened
    exact no_singleton_scope418 a _ scope.candidate.exactVisible

theorem no_old_election_on_rigid_rival418 {s q needs}
    (a : Winner s q) (event : Event s q) : ¬ PlainMerged416.R8.elected s q event needs := by
  obtain ⟨p,out,exactHead,normalized⟩ :=
    every_visible_candidate_is_a_variant_after_normalization418 a event.frame.inScope
  have wrote : p ∈ event.frame.decl.head := by simp [exactHead]
  rintro (((((legacy|named)|list)|whereList)|record)|plain)
  · rcases R0_selection_uses_independent_original_rule407 event legacy with allVariables|native
    · obtain ⟨_,bad,_⟩ := allVariables.2 event.frame.decl event.frame.inScope _ wrote
      rw [bad] at normalized
      cases normalized
    · obtain ⟨fromSyntax⟩ := native
      have same := (List.cons.inj (exactHead.symm.trans fromSyntax.test.writtenHead)).1
      rw [same] at normalized
      change Pattern.app _ _ = Pattern.variant a.rows.tag out at normalized
      cases normalized
  · obtain ⟨_,⟨candidate⟩⟩ := named
    exact no_application_scope418 a event.frame.inScope candidate.test.named rfl
  · obtain ⟨_,⟨candidate⟩⟩ := list
    exact no_application_scope418 a event.frame.inScope candidate.test.named rfl
  · obtain ⟨_,⟨candidate⟩⟩ := whereList
    exact no_application_scope418 a event.frame.inScope candidate.test.named rfl
  · obtain ⟨_,⟨r⟩⟩ := record
    cases r with
    | parent _ parent => exact no_singleton_scope418 a _ parent.candidate.visibleOne
    | leaf _ _ leaf => exact no_singleton_scope418 a _ leaf.candidate.visibleOne
  · obtain ⟨_,⟨r⟩⟩ := plain
    cases r with
    | actual _ plain => exact no_singleton_scope418 a _ plain.candidate.visibleOne

/-- Candidate identity is determined by the whole original visible list,
and plain join syntax cannot be mistaken for the rigid variant form. -/
theorem independent_rival_scans_agree_on_plain_declaration418 {s q}
    (a b : Winner s q) : a.winner.candidate.decl = b.winner.candidate.decl := by
  rcases (actual_candidates_and_no_others418 b _).mp a.winner.candidate.found with same|wrong
  · exact same
  · have eq := (List.cons.inj (a.winner.head.symm.trans
      ((congrArg Declaration.head wrong).trans b.mismatch.rival.literal))).1
    cases eq

theorem old_C09_not_a_second_accepted_diagnosis418 {s q}
    (a : Winner s q) (b : X6Ambiguous417.Ambiguous s q) : False := by
  have same : a.mismatch.rival.candidate.decl = b.ground.candidate.decl := by
    rcases (X6Ambiguous417.actual_matching_candidates_are_exactly_two417 b _).mp
      a.mismatch.rival.candidate.found with nope|ok
    · have impossible := (List.cons.inj (a.mismatch.rival.literal.symm.trans
        ((congrArg Declaration.head nope).trans b.plain.head))).1
      cases impossible
    · exact ok
  have both := (List.cons.inj (a.mismatch.rival.literal.symm.trans
    ((congrArg Declaration.head same).trans b.ground.head))).1
  have sameName := (Pattern.app.inj ((Pattern.variant.inj both).2)).1
  have impossible := a.mismatch.rival.kind
  rw [sameName,b.ground.kind] at impossible
  cases impossible

theorem R9_diagnostics_excluded_by_actual_rigid_rival418 {s q v needs}
    (a : Winner s q) : ¬ X6Ambiguous417.R9.other s q v needs := by
  rintro (old|⟨_,_,⟨twoMatch⟩⟩)
  · exact no_old_diagnostic_on_rigid_rival418 a old
  · exact old_C09_not_a_second_accepted_diagnosis418 a twoMatch

theorem actual_rigid_scan_has_only_the_original_winner418 {s q} (a : Winner s q)
    {t e} (trace : SourceTrace R10 s q t e) :
    t = .selected a.winner.candidate.decl.id [] := by
  cases trace with
  | rootK2 cycle => exact False.elim (X6Ambiguous417.root_safe417 a.inspections cycle)
  | other _ _ rule _ => exact False.elim (R9_diagnostics_excluded_by_actual_rigid_rival418 a rule)
  | selected event _ rule _ kids =>
    rcases rule with prior|⟨_,⟨data⟩⟩
    · exact False.elim (no_old_election_on_rigid_rival418 a event prior)
    · cases data with
      | actual b =>
        have empty := exact_winner_has_no_where418 b
        have noTrees : ∀ {qs ts}, WhereForest R10 s qs ts → qs = [] → ts = [] := by
          intro qs ts forest exactEmpty
          cases forest with
          | nil => rfl
          | cons _ _ => cases exactEmpty
        rw [noTrees kids empty]
        change CommonRoleOutermostResolver.Tree.selected b.winner.candidate.decl.id [] = _
        rw [independent_rival_scans_agree_on_plain_declaration418 b a]

theorem previous_checker_cannot_claim_another_result_for_rigid_winner418
    (p : Problem) (r : Result) (a : Winner p.state p.root) (w : X6Ambiguous417.Witness) :
    X6Ambiguous417.check p r w = false := by
  cases checked : X6Ambiguous417.check p r w with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨e,t,_,_⟩ := (X6Ambiguous417.check_sound p r w checked).1
    generalize r.tree = tree at t
    cases t with
    | rootK2 cyclic => exact X6Ambiguous417.root_safe417 a.inspections cyclic
    | other _ _ localRule _ => exact R9_diagnostics_excluded_by_actual_rigid_rival418 a localRule
    | selected event _ localRule _ _ => exact no_old_election_on_rigid_rival418 a event localRule

theorem rigid_report_is_unique_in_its_checked_scope418 (p : Problem) (a : Winner p.state p.root)
    (r : Result) (w : Witness) (yes : check p r w = true) :
    r = Check408.nullaryReport a.winner.candidate.decl := by
  cases w with
  | previous w =>
    change X6Ambiguous417.check p r w = true at yes
    rw [previous_checker_cannot_claim_another_result_for_rigid_winner418 p r a w] at yes
    cases yes
  | rigidRival fresh =>
    obtain ⟨b,_,report⟩ := checked_plain_merge_reflects_original418 p r fresh yes
    exact report.trans (congrArg Check408.nullaryReport
      (independent_rival_scans_agree_on_plain_declaration418 b a))
  | unsupported => simp [check] at yes

end Yulang.GeneralDeclarativeI65.I72.RigidRival418
