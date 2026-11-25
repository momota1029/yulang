import Yulang.GeneralDeclarativeI65I74PlainMergedBoundary416

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PlainMerged416
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)
open Checker408 (Problem Result)
open RecordK2412 (closedHead412)

theorem visible_plain_head_is_original416 {s q} {a : PlainRows s q} (r : PlainRead a)
    (d : Declaration) (seen : d ∈ visible s.core q) :
    d.head = [sourceX6 a.tag r.first r.second] := by
  rw [r.candidate.visibleOne] at seen
  cases List.mem_singleton.mp seen
  exact r.head

private theorem not_a_variable_scope416 {s q} {a : PlainRows s q} (r : PlainRead a)
    (scope : (d : Declaration) → d ∈ visible s.core q → RepeatedRow403 q d) : False := by
  let d := r.candidate.decl
  have seen : d ∈ visible s.core q := by simp [d,r.candidate.visibleOne]
  have wrote : sourceX6 a.tag r.first r.second ∈ d.head := by simp [d,r.head]
  rw [(scope d seen).literal] at wrote
  obtain ⟨_,_,contradiction⟩ := List.mem_map.mp wrote
  cases contradiction

private theorem not_a_nominal_scope416 {s q} {a : PlainRows s q} (r : PlainRead a)
    {d : Declaration} (seen : d ∈ visible s.core q) {p : Pattern} (written : d.head = [p])
    {key args} (shape : normalize p = .app key args) : False := by
  have single := (List.cons.inj (written.symm.trans (visible_plain_head_is_original416 r d seen))).1
  have noApp := (congrArg normalize single).symm.trans shape
  rw [two_literal_plain_arms_normalize_to_one_actual_tag416 _ _ _ r.differentBinder] at noApp
  cases noApp

private theorem no_repeat_other416 {s q v} {a : PlainRows s q} (r : PlainRead a)
    (old : RepeatedOther403 s q v) : False := by
  cases old with
  | ambiguous scope _ =>
    obtain ⟨s⟩ := scope
    exact not_a_variable_scope416 r s.allVisible

private theorem no_native_other416 {s q v needs} {a : PlainRows s q} (r : PlainRead a)
    (old : variableWithNativeK2403.other s q v needs) : False := by
  rcases old.2 with repeats|⟨_,_,view,_⟩
  · exact no_repeat_other416 r repeats
  · exact not_a_nominal_scope416 r view.visibleRow view.exactHead view.dispatch

private theorem no_closed_native_other416 {s q v needs} {a : PlainRows s q} (r : PlainRead a)
    (old : completedNativePrioritySource404.other s q v needs) : False := by
  rcases old with earlier|⟨_,⟨caller⟩⟩
  · exact no_native_other416 r earlier
  · exact not_a_nominal_scope416 r caller.entry.visibleRow caller.entry.exactHead caller.entry.dispatch

private theorem no_prior_choice_other416 {s q v needs} {a : PlainRows s q} (r : PlainRead a)
    (old : completedChoiceSource404.other s q v needs) : False := by
  rcases old with earlier|⟨_,⟨scope⟩⟩
  · exact no_closed_native_other416 r earlier
  · exact not_a_variable_scope416 r scope.allVisible

theorem no_prior_diagnostic_with_actual_plain_head416 {s q v needs}
    {a : PlainRows s q} (r : PlainRead a) :
    ¬ ClosedResidual415.R7.other s q v needs := by
  rintro (((⟨_,family,old⟩|⟨_,_,⟨closed⟩⟩)|mixed)|opened)
  · cases family with
    | variableOnly =>
      cases old.2 with
      | ambiguous scope _ =>
        obtain ⟨declared⟩ := scope
        let d := r.candidate.decl
        have here : d ∈ visible s.core q := by simp [d,r.candidate.visibleOne]
        have pattern : sourceX6 a.tag r.first r.second ∈ d.head := by simp [d,r.head]
        rw [(declared.allVisible d here).literal] at pattern
        obtain ⟨_,_,no⟩ := List.mem_map.mp pattern
        cases no
    | repeated | whereTree => exact no_repeat_other416 r old.2
    | nativeK2 | supported => exact no_native_other416 r old
    | supportedK2 => exact no_closed_native_other416 r old
    | supportedAmbiguity | authoredNative => exact no_prior_choice_other416 r old
  · have here : closed.decl ∈ visible s.core q := by simp [closed.field.only]
    have impossible := (List.cons.inj ((visible_plain_head_is_original416 r _ here).symm.trans closed.field.head)).1
    cases impossible
  · obtain ⟨_,_,⟨view⟩⟩ := mixed
    have least := view.rivalsExist
    simp [r.candidate.visibleOne] at least
  · obtain ⟨_,_,⟨scope⟩⟩ := opened
    have here : scope.candidate.decl ∈ visible s.core q := by simp [scope.candidate.exactVisible]
    have impossible := (List.cons.inj ((visible_plain_head_is_original416 r _ here).symm.trans scope.candidate.head)).1
    cases impossible

theorem no_prior_selection_with_actual_plain_head416 {s q needs} {a : PlainRows s q}
    (r : PlainRead a) (event : Event s q) :
    ¬ ClosedResidual415.R7.elected s q event needs := by
  have shape := visible_plain_head_is_original416 r event.frame.decl event.frame.inScope
  have written : sourceX6 a.tag r.first r.second ∈ event.frame.decl.head := by simp [shape]
  rintro ((((legacy|named)|list)|whereList)|record)
  · rcases R0_selection_uses_independent_original_rule407 event legacy with plain|native
    · obtain ⟨_,bad,_⟩ := plain.2 event.frame.decl event.frame.inScope _ written
      cases bad
    · obtain ⟨source⟩ := native
      have clash := (List.cons.inj (source.test.writtenHead.symm.trans shape)).1
      cases clash
  · obtain ⟨_,⟨view⟩⟩ := named
    exact not_a_nominal_scope416 r event.frame.inScope view.test.named rfl
  · obtain ⟨_,⟨view⟩⟩ := list
    exact not_a_nominal_scope416 r event.frame.inScope view.test.named rfl
  · obtain ⟨_,⟨view⟩⟩ := whereList
    exact not_a_nominal_scope416 r event.frame.inScope view.test.named rfl
  · obtain ⟨_,⟨read⟩⟩ := record
    cases read with
    | parent rows parent =>
      have clash := (List.cons.inj (shape.symm.trans parent.literal)).1
      cases clash
    | leaf rows parent child =>
      have clash := (List.cons.inj (shape.symm.trans child.literal)).1
      cases clash

theorem plain_branch_preserves_previous_disjointness416 (p : Problem) (r old : Result)
    (w : PlainWire) (prior : ClosedResidual415.Witness)
    (yes : check p r (.plainMerged w) = true) : check p old (.previous prior) = false := by
  obtain ⟨actual,_,_⟩ := checked_plain_merge_reflects_original416 p r w yes
  cases before : ClosedResidual415.check p old prior with
  | false => exact before
  | true =>
    exfalso
    obtain ⟨e,t,_,_⟩ := (ClosedResidual415.check_sound p old prior before).1
    generalize old.tree = tree at t
    cases t with
    | rootK2 cycle => exact actual.rootSafe cycle
    | other _ _ previous _ => exact no_prior_diagnostic_with_actual_plain_head416 actual.actual previous
    | selected event _ previous _ _ =>
      exact no_prior_selection_with_actual_plain_head416 actual.actual event previous

end Yulang.GeneralDeclarativeI65.I72.PlainMerged416
