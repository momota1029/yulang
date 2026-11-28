import Yulang.GeneralDeclarativeI65I74G05OrderedSafeChoices490
import Yulang.GeneralDeclarativeI65I74G05ExactOutcomePartition490
import Yulang.GeneralDeclarativeI65I74G05SemanticTransport488

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint)

theorem every_exact_g05_safe_choice_reifies_a_full_wire_and_reaches_its_own_ordered_continuation490
    {n : Nat} {α : Type} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (next : List (Nat × G05LocalVerdict487) → α)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (meaning : G05LocalMeaning487) (protocol : G05ExactLocalProtocol487 test meaning)
    (choices : G05OrderedLocalChoices490 p)
    (allowedChoices : G05OrderedSafeChoices490 p gd pos rel coords Allowed meaning choices) :
    ∃ r w, w.roots.map Checkpoint.which = coords ∧
      G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r ∧
      r.priority = .eligible (List.ofFn choices) ∧
      checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inr w) = true ∧
      routeG05WithDeferredLocal489 p gd pos rel coords permit test (fun _ => some (r,w)) next =
        .continued (next (List.ofFn choices)) := by
  obtain ⟨r,exactReport,marked⟩ :=
    every_independently_permitted_g05_safe_choice_list_has_an_exact_report490 scope meaning choices allowedChoices
  obtain ⟨w,roots,verified⟩ :=
    independently_exact_g05_reports_reify_without_an_observation_order_or_arity_assumption488
      p gd pos rel coords permit test Allowed meaning scope protocol r exactReport
  refine ⟨r,w,roots,exactReport,marked,verified,?_⟩
  exact (verified_deferred_g05_continuation_iff_full_check_and_eligible_ordered_marks489
    p gd pos rel coords permit test (fun _ => some (r,w)) next Allowed scope
    (next (List.ofFn choices))).mpr ⟨r,w,List.ofFn choices,rfl,verified,marked,rfl⟩

theorem all_observable_successful_g05_continuations_transfer_between_exact_local_protocols490
    {n : Nat} {α : Type} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permitLeft permitRight : Nat → CandidateVisitKey485 n → Bool)
    (left right : G05LocalChecker487) (next : List (Nat × G05LocalVerdict487) → α)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scopeLeft : G05ExactVisitInputs487 p gd pos rel coords permitLeft Allowed)
    (scopeRight : G05ExactVisitInputs487 p gd pos rel coords permitRight Allowed)
    (meaning : G05LocalMeaning487)
    (leftExact : G05ExactLocalProtocol487 left meaning)
    (rightExact : G05ExactLocalProtocol487 right meaning) (value : α) :
    (∃ supply, routeG05WithDeferredLocal489 p gd pos rel coords permitLeft left supply next = .continued value) ↔
      ∃ supply, routeG05WithDeferredLocal489 p gd pos rel coords permitRight right supply next = .continued value := by
  have transfer : ∀ (p0 p1 : Nat → CandidateVisitKey485 n → Bool) (c0 c1 : G05LocalChecker487),
      G05ExactVisitInputs487 p gd pos rel coords p0 Allowed →
      G05ExactVisitInputs487 p gd pos rel coords p1 Allowed →
      G05ExactLocalProtocol487 c0 meaning → G05ExactLocalProtocol487 c1 meaning →
      (∃ supply, routeG05WithDeferredLocal489 p gd pos rel coords p0 c0 supply next = .continued value) →
      ∃ supply, routeG05WithDeferredLocal489 p gd pos rel coords p1 c1 supply next = .continued value := by
    rintro p0 p1 c0 c1 s0 s1 e0 e1 ⟨supply,ran⟩
    obtain ⟨r,w,marks,_,accepted,eligible,emit⟩ :=
      (verified_deferred_g05_continuation_iff_full_check_and_eligible_ordered_marks489
        p gd pos rel coords p0 c0 supply next Allowed s0 value).mp ran
    have roots := (verified_g05_report_has_exact_original_coordinates_and_evidence_for_all_fitting_models488
      Allowed s0 meaning e0 (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ _ => True.intro) accepted).1
    obtain ⟨fresh,_,rechecked⟩ :=
      (exact_g05_acceptance_can_transport_between_protocol_encodings_of_the_same_source488
        p gd pos rel coords p0 p1 c0 c1 Allowed meaning s0 s1 e0 e1 r).mp ⟨w,roots,accepted⟩
    exact ⟨fun _ => some (r,fresh),
      (verified_deferred_g05_continuation_iff_full_check_and_eligible_ordered_marks489
        p gd pos rel coords p1 c1 (fun _ => some (r,fresh)) next Allowed s1 value).mpr
        ⟨r,fresh,marks,rfl,rechecked,eligible,emit⟩⟩
  exact ⟨transfer permitLeft permitRight left right scopeLeft scopeRight leftExact rightExact,
    transfer permitRight permitLeft right left scopeRight scopeLeft rightExact leftExact⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
