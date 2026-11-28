import Yulang.GeneralDeclarativeI65I74G05RefusalBoundary490
import Yulang.GeneralDeclarativeI65I74G05ReportExistence489

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

theorem a_deferred_g05_route_rejects_some_k2_iff_some_original_slot_really_recurs490
    {n : Nat} {α : Type} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (supply : Unit → Option (G05Report487 n × G05FiniteWitness487 n))
    (next : List (Nat × G05LocalVerdict487) → α)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed) :
    (∃ hits, routeG05WithDeferredLocal489 p gd pos rel coords permit test supply next = .blockedByK2 hits) ↔
      ∃ i : Fin (visible485 p).length, IndependentScopedReturn487 p gd pos rel coords Allowed i.val := by
  constructor
  · rintro ⟨hits,blocked⟩
    obtain ⟨nonempty,_,each,_⟩ :=
      exact_deferred_g05_refusal_has_all_and_only_original_hits_with_same_fit_returns490
        p gd pos rel coords permit test supply next Allowed scope hits blocked
    cases hits with
    | nil => exact False.elim (nonempty rfl)
    | cons first rest =>
      obtain ⟨i,_,recurs⟩ := (each first).mp (List.mem_cons_self ..)
      exact ⟨i,recurs⟩
  · rintro ⟨i,recurs⟩
    have nonempty : coords ≠ [] := by
      intro empty
      subst coords
      exact empty_original_g05_coordinates_never_have_an_independent_candidate_recursion489 i.val recurs
    obtain ⟨hits,ran,_⟩ :=
      a_real_independent_g05_k2_on_nonempty_original_demand_replays_without_any_local_matcher489
        p gd pos rel coords permit Allowed scope nonempty i recurs
    exact ⟨hits,
      a_positive_g05_preflight_needs_neither_a_local_checker_nor_a_full_report_supplier489 ran test supply next⟩

/-- If verification did not replay, there is no actual K2 and the
particular supplied full input did not verify. This says nothing about
availability of another witness, or the verdict in an unverified report. -/
theorem exact_deferred_g05_nonreplay_iff_no_actual_k2_and_no_accepted_supplied_report490
    {n : Nat} {α : Type} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (supply : Unit → Option (G05Report487 n × G05FiniteWitness487 n))
    (next : List (Nat × G05LocalVerdict487) → α)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed) :
    routeG05WithDeferredLocal489 p gd pos rel coords permit test supply next = .notReplayed ↔
      (∀ i : Fin (visible485 p).length, ¬ IndependentScopedReturn487 p gd pos rel coords Allowed i.val) ∧
      ¬ ∃ r w, supply () = some (r,w) ∧
        checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inr w) = true := by
  have blocked := a_deferred_g05_route_rejects_some_k2_iff_some_original_slot_really_recurs490
    p gd pos rel coords permit test supply next Allowed scope
  constructor
  · intro none
    refine ⟨fun i has => ?_,?_⟩
    · obtain ⟨hits,conflict⟩ := blocked.mpr ⟨i,has⟩
      rw [none] at conflict
      cases conflict
    · rintro ⟨r,w,provided,good⟩
      have same :=
        (deferred_g05_route_is_equal_to_eager_route_when_full_input_is_already_supplied489
          p gd pos rel coords permit test r w supply provided next).trans
        (early_g05_priority_preserves_every_verified_full_route_under_exact_visits489
          p gd pos rel coords permit test Allowed scope r w good next)
      rw [none] at same
      cases ordinal : r.priority <;>
        simp [routeFromCheckedG05Report488,good,ordinal] at same
  · rintro ⟨safe,noValidFull⟩
    cases out : routeG05WithDeferredLocal489 p gd pos rel coords permit test supply next with
    | notReplayed => rfl
    | blockedByK2 hits =>
      obtain ⟨i,cycle⟩ := blocked.mp ⟨hits,out⟩
      exact False.elim (safe i cycle)
    | continued value =>
      obtain ⟨r,w,_,gave,good,_,_⟩ :=
        (verified_deferred_g05_continuation_iff_full_check_and_eligible_ordered_marks489
          p gd pos rel coords permit test supply next Allowed scope value).mp out
      exact False.elim (noValidFull ⟨r,w,gave,good⟩)

theorem an_exact_g05_deferred_route_with_some_source_cycle_is_independent_of_any_local_implementation490
    {n : Nat} {α : Type} {β : Type} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool)
    (left right : G05LocalChecker487)
    (supplyLeft supplyRight : Unit → Option (G05Report487 n × G05FiniteWitness487 n))
    (nextLeft : List (Nat × G05LocalVerdict487) → α)
    (nextRight : List (Nat × G05LocalVerdict487) → β)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (someone : ∃ i : Fin (visible485 p).length, IndependentScopedReturn487 p gd pos rel coords Allowed i.val) :
    ∃ hits, routeG05WithDeferredLocal489 p gd pos rel coords permit left supplyLeft nextLeft = .blockedByK2 hits ∧
      routeG05WithDeferredLocal489 p gd pos rel coords permit right supplyRight nextRight = .blockedByK2 hits := by
  obtain ⟨hits,first⟩ := (a_deferred_g05_route_rejects_some_k2_iff_some_original_slot_really_recurs490
    p gd pos rel coords permit left supplyLeft nextLeft Allowed scope).mpr someone
  have ran := (exact_deferred_g05_refusal_iff_original_preflight_refusal490
    p gd pos rel coords permit left supplyLeft nextLeft Allowed scope hits).mp first
  exact ⟨hits,first,
    a_positive_g05_preflight_needs_neither_a_local_checker_nor_a_full_report_supplier489 ran right supplyRight nextRight⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
