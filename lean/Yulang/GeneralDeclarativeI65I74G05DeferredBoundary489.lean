import Yulang.GeneralDeclarativeI65I74G05DeferredEntry489
import Yulang.GeneralDeclarativeI65I74G05PreflightCompatibility489

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

theorem verified_deferred_g05_continuation_iff_full_check_and_eligible_ordered_marks489
    {n : Nat} {α : Type} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool)
    (test : G05LocalChecker487) (supply : Unit → Option (G05Report487 n × G05FiniteWitness487 n))
    (next : List (Nat × G05LocalVerdict487) → α)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed) (value : α) :
    routeG05WithDeferredLocal489 p gd pos rel coords permit test supply next = .continued value ↔
      ∃ r w marks, supply () = some (r,w) ∧
        checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inr w) = true ∧
        r.priority = .eligible marks ∧ next marks = value := by
  constructor
  · intro continued
    unfold routeG05WithDeferredLocal489 at continued
    split at continued
    · cases continued
    · cases supplied : supply () with
      | none => simp [supplied] at continued
      | some full =>
        obtain ⟨r,w⟩ := full
        simp only [supplied] at continued
        unfold routeFromCheckedG05Report488 at continued
        split at continued
        · rename_i checked
          cases status : r.priority with
          | recursive hits => simp [status] at continued
          | eligible marks =>
            exact ⟨r,w,marks,rfl,checked,status,by simpa [status] using continued⟩
        · cases continued
  · rintro ⟨r,w,marks,ready,checked,eligible,chosen⟩
    rw [deferred_g05_route_is_equal_to_eager_route_when_full_input_is_already_supplied489
        p gd pos rel coords permit test r w supply ready next,
      early_g05_priority_preserves_every_verified_full_route_under_exact_visits489
        p gd pos rel coords permit test Allowed scope r w checked next,
      continuation_of_a_verified_g05_report_keeps_the_exact_ordered_marks488 checked eligible next,
      chosen]

theorem deferred_g05_continuation_preserves_the_independent_nonrecursive_rule_for_every_candidate489
    {n : Nat} {α : Type} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool}
    {test : G05LocalChecker487} {supply : Unit → Option (G05Report487 n × G05FiniteWitness487 n)}
    {next : List (Nat × G05LocalVerdict487) → α} {value : α}
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (meaning : G05LocalMeaning487) (protocol : G05ExactLocalProtocol487 test meaning)
    (result : routeG05WithDeferredLocal489 p gd pos rel coords permit test supply next = .continued value) :
    (∀ i : Fin (visible485 p).length, ¬ IndependentScopedReturn487 p gd pos rel coords Allowed i.val) ∧
    ∃ r marks, G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r ∧
      r.priority = .eligible marks ∧ next marks = value := by
  obtain ⟨r,w,marks,_,checked,eligible,chosen⟩ :=
    (verified_deferred_g05_continuation_iff_full_check_and_eligible_ordered_marks489
      p gd pos rel coords permit test supply next Allowed scope value).mp result
  have full := (verified_g05_report_has_exact_original_coordinates_and_evidence_for_all_fitting_models488
    Allowed scope meaning protocol (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ _ => True.intro) checked).2.1
  exact ⟨eligible_report_excludes_every_independently_visited_k2_cycle488 full eligible,
    r,marks,full,eligible,chosen⟩

theorem empty_original_g05_coordinates_never_have_an_independent_candidate_recursion489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)}
    {Allowed : Nat → CandidateVisitKey485 n → Prop} (i : Nat) :
    ¬ IndependentScopedReturn487 p gd pos rel [] Allowed i := by
  rintro ⟨_,_,_,_,_,impossible,_⟩
  cases impossible

theorem empty_coordinates_never_create_an_early_positive_g05_classification489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} (hits : List Nat) :
    readG05Preflight489 p gd pos rel [] permit ≠ some (.recursive hits) := by
  intro classified
  let available : Nat → CandidateVisitKey485 n → Prop := fun ordinal key => permit ordinal key = true
  obtain ⟨nonempty,exactHits⟩ := a_successful_positive_g05_preflight_lists_every_and_only_the_actual_original_k2_slots489
    classified available (fun _ _ => Iff.rfl)
  cases hits with
  | nil => exact nonempty rfl
  | cons ord tail =>
    obtain ⟨i,_,falseHit⟩ := (exactHits ord).mp (List.mem_cons_self ..)
    exact empty_original_g05_coordinates_never_have_an_independent_candidate_recursion489 i.val falseHit

theorem eager_g05_preflight_preserves_every_empty_demand_behavior_without_any_source_assumption489
    {n : Nat} {α : Type} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (r : G05Report487 n) (w : G05FiniteWitness487 n)
    (next : List (Nat × G05LocalVerdict487) → α) :
    routeG05PreflightThenChecked489 p gd pos rel [] permit test r w next =
      routeFromCheckedG05Report488 p gd pos rel [] permit test r w next := by
  unfold routeG05PreflightThenChecked489
  split
  · rename_i hits scanned
    exact False.elim (empty_coordinates_never_create_an_early_positive_g05_classification489 hits scanned)
  · rfl

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
