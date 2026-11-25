import Yulang.GeneralDeclarativeI65I74X6AmbiguousEntry417
import Yulang.GeneralDeclarativeI65I74PlainMergedPriority416

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)
open Checker408 (Problem Result)
open RecordK2412 (closedHead412)

open PlainMerged416 (sourceX6 two_literal_plain_arms_normalize_to_one_actual_tag416)

theorem every_visible_candidate_is_a_variant_after_normalization417 {s q}
    (a : Ambiguous s q) {d : Declaration} (seen : d ∈ visible s.core q) :
    ∃ p out, d.head = [p] ∧ normalize p = .variant a.rows.tag out := by
  rcases (actual_matching_candidates_are_exactly_two417 a d).mp seen with rfl|rfl
  · exact ⟨_,_,a.plain.head,two_literal_plain_arms_normalize_to_one_actual_tag416 _ _ _ a.plain.unlike⟩
  · exact ⟨_,_,a.ground.head,rfl⟩

private theorem no_variable_scope417 {s q} (a : Ambiguous s q)
    (scope : (d : Declaration) → d ∈ visible s.core q → RepeatedRow403 q d) : False := by
  let d := a.plain.candidate.decl
  have wrote : sourceX6 a.rows.tag a.plain.first a.plain.second ∈ d.head := by simp [d,a.plain.head]
  rw [(scope d a.plain.candidate.found).literal] at wrote
  obtain ⟨_,_,contradiction⟩ := List.mem_map.mp wrote
  cases contradiction

private theorem no_application_scope417 {s q} (a : Ambiguous s q)
    {d : Declaration} (seen : d ∈ visible s.core q) {p : Pattern} (written : d.head = [p])
    {key args} (shape : normalize p = .app key args) : False := by
  obtain ⟨w,n,exactHead,normalized⟩ := every_visible_candidate_is_a_variant_after_normalization417 a seen
  have same := (List.cons.inj (written.symm.trans exactHead)).1
  rw [same,normalized] at shape
  cases shape

private theorem no_record_scope417 {s q} (a : Ambiguous s q)
    {d : Declaration} (seen : d ∈ visible s.core q) {k payload tail}
    (head : d.head = [.record k payload tail]) : False := by
  obtain ⟨p,out,exactHead,normalized⟩ := every_visible_candidate_is_a_variant_after_normalization417 a seen
  have same := (List.cons.inj (exactHead.symm.trans head)).1
  rw [same] at normalized
  change .record k _ _ = Pattern.variant a.rows.tag out at normalized
  cases normalized

private theorem no_singleton_scope417 {s q} (a : Ambiguous s q) (d : Declaration)
    (single : visible s.core q = [d]) : False := by
  have count := congrArg List.length single
  rcases a.ordered with h|h <;> simp [h] at count

private theorem no_repeat_other417 {s q v} (a : Ambiguous s q)
    (old : RepeatedOther403 s q v) : False := by
  cases old with
  | ambiguous scope _ =>
    obtain ⟨s⟩ := scope
    exact no_variable_scope417 a s.allVisible

private theorem no_native_other417 {s q v needs} (a : Ambiguous s q)
    (old : variableWithNativeK2403.other s q v needs) : False := by
  rcases old.2 with repeats|⟨_,_,view,_⟩
  · exact no_repeat_other417 a repeats
  · exact no_application_scope417 a view.visibleRow view.exactHead view.dispatch

private theorem no_closed_native_other417 {s q v needs} (a : Ambiguous s q)
    (old : completedNativePrioritySource404.other s q v needs) : False := by
  rcases old with earlier|⟨_,⟨caller⟩⟩
  · exact no_native_other417 a earlier
  · exact no_application_scope417 a caller.entry.visibleRow caller.entry.exactHead caller.entry.dispatch

private theorem no_prior_choice_other417 {s q v needs} (a : Ambiguous s q)
    (old : completedChoiceSource404.other s q v needs) : False := by
  rcases old with earlier|⟨_,⟨scope⟩⟩
  · exact no_closed_native_other417 a earlier
  · exact no_variable_scope417 a scope.allVisible

theorem no_old_diagnostic_when_both_X6_heads_match417 {s q verdict needs}
    (a : Ambiguous s q) : ¬ PlainMerged416.R8.other s q verdict needs := by
  rintro (((⟨_,family,old⟩|⟨_,_,⟨single⟩⟩)|mixed)|opened)
  · cases family with
    | variableOnly =>
      cases old.2 with
      | ambiguous scope _ =>
        obtain ⟨declared⟩ := scope
        let d := a.plain.candidate.decl
        have wrote : sourceX6 a.rows.tag a.plain.first a.plain.second ∈ d.head :=
          by simp [d,a.plain.head]
        rw [(declared.allVisible d a.plain.candidate.found).literal] at wrote
        obtain ⟨_,_,contradiction⟩ := List.mem_map.mp wrote
        cases contradiction
    | repeated | whereTree => exact no_repeat_other417 a old.2
    | nativeK2 | supported => exact no_native_other417 a old
    | supportedK2 => exact no_closed_native_other417 a old
    | supportedAmbiguity | authoredNative => exact no_prior_choice_other417 a old
  · exact no_singleton_scope417 a _ single.field.only
  · obtain ⟨_,_,⟨view⟩⟩ := mixed
    let d := view.tape.opening.decl
    have seen : d ∈ visible s.core q := List.mem_of_getElem? view.tape.opening.fromOriginalList
    obtain ⟨_,_,_,h⟩ := view.tape.record_head d seen
    exact no_record_scope417 a seen h
  · obtain ⟨_,_,⟨scope⟩⟩ := opened
    exact no_singleton_scope417 a _ scope.candidate.exactVisible

theorem no_prior_selection_when_both_X6_heads_match417 {s q needs}
    (a : Ambiguous s q) (event : Event s q) : ¬ PlainMerged416.R8.elected s q event needs := by
  obtain ⟨p,out,exactHead,normalized⟩ :=
    every_visible_candidate_is_a_variant_after_normalization417 a event.frame.inScope
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
    exact no_application_scope417 a event.frame.inScope candidate.test.named rfl
  · obtain ⟨_,⟨candidate⟩⟩ := list
    exact no_application_scope417 a event.frame.inScope candidate.test.named rfl
  · obtain ⟨_,⟨candidate⟩⟩ := whereList
    exact no_application_scope417 a event.frame.inScope candidate.test.named rfl
  · obtain ⟨_,⟨r⟩⟩ := record
    cases r with
    | parent _ parent => exact no_singleton_scope417 a _ parent.candidate.visibleOne
    | leaf _ _ leaf => exact no_singleton_scope417 a _ leaf.candidate.visibleOne
  · obtain ⟨_,⟨r⟩⟩ := plain
    cases r with
    | actual _ plain => exact no_singleton_scope417 a _ plain.candidate.visibleOne

theorem actual_X6_has_only_ambiguity_in_R9_417 {s q} (a : Ambiguous s q)
    {t e} (trace : SourceTrace R9 s q t e) : t = .ambiguous ∧ e = none := by
  cases trace with
  | rootK2 cycle => exact False.elim (root_safe417 a.visits cycle)
  | selected e _ rule _ _ =>
    exact False.elim (no_prior_selection_when_both_X6_heads_match417 a e rule)
  | other verdict _ rule _ =>
    rcases rule with old|⟨rfl,_,_⟩
    · exact False.elim (no_old_diagnostic_when_both_X6_heads_match417 a old)
    · exact ⟨rfl,rfl⟩

theorem old_checker_cannot_claim_another_result_for_actual_X6_417 (p : Problem) (r : Result)
    (a : Ambiguous p.state p.root) (old : PlainMerged416.Witness) :
    PlainMerged416.check p r old = false := by
  cases before : PlainMerged416.check p r old with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨e,t,_,_⟩ := (PlainMerged416.check_sound p r old before).1
    generalize r.tree = tree at t
    cases t with
    | rootK2 cycle => exact root_safe417 a.visits cycle
    | other _ _ prior _ => exact no_old_diagnostic_when_both_X6_heads_match417 a prior
    | selected event _ prior _ _ =>
      exact no_prior_selection_when_both_X6_heads_match417 a event prior

theorem every_certified_result_for_actual_X6_is_the_canonical_ambiguity417
    (p : Problem) (a : Ambiguous p.state p.root) (r : Result) (w : Witness)
    (yes : check p r w = true) : r = report417 := by
  cases w with
  | previous old =>
    change PlainMerged416.check p r old = true at yes
    rw [old_checker_cannot_claim_another_result_for_actual_X6_417 p r a old] at yes
    cases yes
  | x6Ambiguity w =>
    exact (checked_x6_reflects_exact_candidates_and_report417 p r w yes).choose_spec.2
  | unsupported => simp [check] at yes

end Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417
