import Yulang.GeneralDeclarativeI65I74G05DeferredBoundary489
import Yulang.GeneralDeclarativeI65I74G05AuthoredOrder489
import Yulang.GeneralDeclarativeI65I74G05SameFitK2Return489

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

private theorem full_recursive_route_implies_a_real_source_slot490
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {test : G05LocalChecker487}
    {r : G05Report487 n} {w : G05FiniteWitness487 n} {hits : List Nat}
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (checked : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inr w) = true)
    (priority : r.priority = .recursive hits) :
    ∃ i : Fin (visible485 p).length, IndependentScopedReturn487 p gd pos rel coords Allowed i.val := by
  obtain ⟨signed,shape⟩ :=
    every_accepted_g05_full_report_has_original_signed_projection_without_local_protocol489 Allowed scope checked
  obtain ⟨eq,nonempty⟩ :=
    (recursive_report_keeps_the_whole_original_ordered_hit_list488 r hits shape).mp priority
  cases hits with
  | nil => exact False.elim (nonempty rfl)
  | cons ord rest =>
    have member : ord ∈ positiveOrdinals485 (g05SignsOfReport489 r) := by
      rw [positive_signs_of_g05_report_are_its_whole_original_ordered_hit_list489,←eq]
      exact List.mem_cons_self ..
    obtain ⟨i,_,real⟩ :=
      (an_original_ordinal_is_positive_exactly_when_its_visible_slot_really_recurs489 signed ord).mp member
    exact ⟨i,real⟩

/-- Even a supplied full report cannot introduce a second way to declare K2.
The equivalence is about the original demand, including zero arguments. -/
theorem exact_deferred_g05_refusal_iff_original_preflight_refusal490
    {n : Nat} {α : Type} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (supply : Unit → Option (G05Report487 n × G05FiniteWitness487 n))
    (next : List (Nat × G05LocalVerdict487) → α)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed) (hits : List Nat) :
    routeG05WithDeferredLocal489 p gd pos rel coords permit test supply next = .blockedByK2 hits ↔
      readG05Preflight489 p gd pos rel coords permit = some (.recursive hits) := by
  constructor
  · intro blocked
    unfold routeG05WithDeferredLocal489 at blocked
    split at blocked
    · rename_i prior found
      have agree := G05Continuation488.blockedByK2.inj blocked
      exact agree ▸ found
    · rename_i noPrior
      cases supplied : supply () with
      | none => simp [supplied] at blocked
      | some item =>
        obtain ⟨r,w⟩ := item
        simp only [supplied] at blocked
        unfold routeFromCheckedG05Report488 at blocked
        split at blocked
        · rename_i checked
          cases priority : r.priority with
          | eligible marks => simp [priority] at blocked
          | recursive ords =>
            obtain ⟨i,real⟩ := full_recursive_route_implies_a_real_source_slot490 Allowed scope checked priority
            have nonempty : coords ≠ [] := by
              intro empty
              subst coords
              exact empty_original_g05_coordinates_never_have_an_independent_candidate_recursion489 i.val real
            obtain ⟨actual,replayed,_,_,_,_⟩ :=
              a_real_independent_g05_k2_on_nonempty_original_demand_replays_without_any_local_matcher489
                p gd pos rel coords permit Allowed scope nonempty i real
            exact False.elim (noPrior actual replayed)
        · cases blocked
  · intro ran
    exact a_positive_g05_preflight_needs_neither_a_local_checker_nor_a_full_report_supplier489 ran test supply next

theorem exact_deferred_g05_refusal_has_all_and_only_original_hits_with_same_fit_returns490
    {n : Nat} {α : Type} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (supply : Unit → Option (G05Report487 n × G05FiniteWitness487 n))
    (next : List (Nat × G05LocalVerdict487) → α)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed) (hits : List Nat)
    (blocked : routeG05WithDeferredLocal489 p gd pos rel coords permit test supply next = .blockedByK2 hits) :
    hits ≠ [] ∧ List.Pairwise (· < ·) hits ∧
    (∀ ord, ord ∈ hits ↔ ∃ i : Fin (visible485 p).length,
      (∃ d, OriginalRosterCell485 p i.val (ord,d)) ∧
      IndependentScopedReturn487 p gd pos rel coords Allowed i.val) ∧
    ∀ ord ∈ hits, G05OriginalK2SlotProof489 p gd pos rel coords Allowed ord := by
  have ran := (exact_deferred_g05_refusal_iff_original_preflight_refusal490
    p gd pos rel coords permit test supply next Allowed scope hits).mp blocked
  obtain ⟨notEmpty,each⟩ :=
    a_successful_positive_g05_preflight_lists_every_and_only_the_actual_original_k2_slots489 ran Allowed scope.1
  exact ⟨notEmpty,successful_g05_k2_hits_are_strictly_ordered_without_duplicates489 ran Allowed scope.1,
    each, fun ord inHits =>
      every_early_g05_hit_has_same_fit_constructor_return_at_its_actual_original_slot489 ran Allowed scope.1 ord inHits⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
