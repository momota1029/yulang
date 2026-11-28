import Yulang.GeneralDeclarativeI65I74G05ChoiceReification490

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

theorem every_independent_eligible_g05_report_reflects_exact_ordered_original_local_choices490
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {Allowed : Nat → CandidateVisitKey485 n → Prop} {meaning : G05LocalMeaning487}
    {r : G05Report487 n} {marks : List (Nat × G05LocalVerdict487)}
    (exactReport : G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r)
    (eligible : r.priority = .eligible marks) :
    ∃ choices : G05OrderedLocalChoices490 p,
      G05OrderedSafeChoices490 p gd pos rel coords Allowed meaning choices ∧ List.ofFn choices = marks := by
  classical
  have safe := eligible_report_excludes_every_independently_visited_k2_cycle488 exactReport eligible
  have data : ∀ i : Fin (visible485 p).length, ∃ choice : Nat × G05LocalVerdict487,
      (∃ row, r.rows[i.val]? = some row ∧ row.ordinal = choice.1 ∧ row.mark = .nonrecursive choice.2) ∧
      ∃ d, OriginalRosterCell485 p i.val (choice.1,d) ∧ meaning i.val choice.1 d choice.2 := by
    intro i
    obtain ⟨row,d,there,original,_,marked⟩ := exactReport.2.2 i
    cases says : row.mark with
    | requiredCycle =>
      rw [says] at marked
      exact False.elim (safe i marked)
    | nonrecursive v =>
      rw [says] at marked
      exact ⟨(row.ordinal,v),⟨row,there,rfl,says⟩,d,original,marked.2⟩
  let choices := fun i => Classical.choose (data i)
  have marksOfRows := g05_priority_keeps_every_ordered_original_local_choice490 exactReport.2.1 choices
    (fun i => (Classical.choose_spec (data i)).1)
  exact ⟨choices,fun i => ⟨safe i,(Classical.choose_spec (data i)).2⟩,
    G05Priority487.eligible.inj (marksOfRows.symm.trans (exactReport.1.symm.trans eligible))⟩

/-- Quantifies over suppliers, not an assertion that an arbitrary callback
will deliver the evidence. Any permitted ordered local outcome, and only
such an outcome, can be handed on. -/
theorem attainable_g05_continuation_values_are_exactly_the_independent_ordered_original_choices490
    {n : Nat} {α : Type} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (next : List (Nat × G05LocalVerdict487) → α)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (meaning : G05LocalMeaning487) (protocol : G05ExactLocalProtocol487 test meaning) (value : α) :
    (∃ supply, routeG05WithDeferredLocal489 p gd pos rel coords permit test supply next = .continued value) ↔
      ∃ choices : G05OrderedLocalChoices490 p,
        G05OrderedSafeChoices490 p gd pos rel coords Allowed meaning choices ∧ next (List.ofFn choices) = value := by
  constructor
  · rintro ⟨supply,ran⟩
    obtain ⟨_,r,marks,exactReport,eligible,emit⟩ :=
      deferred_g05_continuation_preserves_the_independent_nonrecursive_rule_for_every_candidate489
        Allowed scope meaning protocol ran
    obtain ⟨choices,good,which⟩ :=
      every_independent_eligible_g05_report_reflects_exact_ordered_original_local_choices490 exactReport eligible
    exact ⟨choices,good,which ▸ emit⟩
  · rintro ⟨choices,good,emit⟩
    obtain ⟨r,w,_,_,_,_,replayed⟩ :=
      every_exact_g05_safe_choice_reifies_a_full_wire_and_reaches_its_own_ordered_continuation490
        p gd pos rel coords permit test next Allowed scope meaning protocol choices good
    exact ⟨fun _ => some (r,w),emit ▸ replayed⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
