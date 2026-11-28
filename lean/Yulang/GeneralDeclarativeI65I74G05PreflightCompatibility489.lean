import Yulang.GeneralDeclarativeI65I74G05ExactPreflightHits489

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

theorem independent_g05_reports_have_identical_k2_signs_across_different_local_meanings489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {Allowed : Nat → CandidateVisitKey485 n → Prop} {left right : G05LocalMeaning487}
    {a b : G05Report487 n}
    (aExact : G05ExactCandidateReport487 p gd pos rel coords Allowed left a)
    (bExact : G05ExactCandidateReport487 p gd pos rel coords Allowed right b) :
    g05SignsOfReport489 a = g05SignsOfReport489 b :=
  exact_g05_signed_roster_is_unique_in_original_order489
    (independent_full_g05_report_has_exact_original_signed_roster489 aExact)
    (independent_full_g05_report_has_exact_original_signed_roster489 bExact)

theorem any_successful_preflight_matches_the_full_report_signs_in_exact_original_order489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {out : PreElection485}
    {Allowed : Nat → CandidateVisitKey485 n → Prop} {meaning : G05LocalMeaning487} {r : G05Report487 n}
    (scan : readG05Preflight489 p gd pos rel coords permit = some out)
    (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key)
    (full : G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r) :
    out = gate485 (g05SignsOfReport489 r) := by
  obtain ⟨_,bits,ledger,gate⟩ := g05_preflight_has_the_actual_roots_and_independent_ordered_signs489 scan Allowed lawful
  have agree := exact_g05_signed_roster_is_unique_in_original_order489 ledger
    (independent_full_g05_report_has_exact_original_signed_roster489 full)
  exact gate.symm.trans (congrArg gate485 agree)

theorem any_successful_preflight_and_exact_g05_report_return_the_same_recursive_list489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {out : PreElection485}
    {Allowed : Nat → CandidateVisitKey485 n → Prop} {meaning : G05LocalMeaning487} {r : G05Report487 n}
    (scan : readG05Preflight489 p gd pos rel coords permit = some out)
    (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key)
    (full : G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r)
    (hits : List Nat) :
    out = .recursive hits ↔ r.priority = .recursive hits := by
  rw [any_successful_preflight_matches_the_full_report_signs_in_exact_original_order489 scan lawful full]
  rw [signed_gate_recursive_iff_it_returns_the_nonempty_exact_positive_subsequence489,
    positive_signs_of_g05_report_are_its_whole_original_ordered_hit_list489]
  exact (recursive_report_keeps_the_whole_original_ordered_hit_list488 r hits full.1).symm

/-- Only the signed projection is used. No independent choice of local
verdict and no matching completeness hypothesis is needed for this fact. -/
theorem every_accepted_g05_full_report_has_original_signed_projection_without_local_protocol489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {test : G05LocalChecker487}
    {r : G05Report487 n} {w : G05FiniteWitness487 n}
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (checked : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inr w) = true) :
    G05ExactSignedRoster489 p (IndependentScopedReturn487 p gd pos rel coords Allowed)
      (g05SignsOfReport489 r) ∧ r.priority = G05PriorityOfRows487 r.rows := by
  let receipt : G05LocalMeaning487 := fun i ord d v => ∃ data, test i ord d data = some v
  have available : G05ExactLocalProtocol487 test receipt :=
    ⟨fun _ _ _ data _ ran => ⟨data,ran⟩,fun _ _ _ _ ran => ran⟩
  have full := (verified_g05_report_has_exact_original_coordinates_and_evidence_for_all_fitting_models488
    Allowed scope receipt available (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ _ => True.intro) checked).2.1
  exact ⟨independent_full_g05_report_has_exact_original_signed_roster489 full,full.1⟩

theorem early_g05_priority_preserves_every_verified_full_route_under_exact_visits489
    {n : Nat} {α : Type} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (r : G05Report487 n) (w : G05FiniteWitness487 n)
    (checked : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inr w) = true)
    (next : List (Nat × G05LocalVerdict487) → α) :
    routeG05PreflightThenChecked489 p gd pos rel coords permit test r w next =
      routeFromCheckedG05Report488 p gd pos rel coords permit test r w next := by
  unfold routeG05PreflightThenChecked489
  cases ran : readG05Preflight489 p gd pos rel coords permit with
  | none => rfl
  | some out =>
    cases out with
    | allSafe ordinals => rfl
    | recursive hits =>
      obtain ⟨reportSigns,priority⟩ :=
        every_accepted_g05_full_report_has_original_signed_projection_without_local_protocol489 Allowed scope checked
      obtain ⟨_,bits,scanned,gate⟩ :=
        g05_preflight_has_the_actual_roots_and_independent_ordered_signs489 ran Allowed scope.1
      rw [exact_g05_signed_roster_is_unique_in_original_order489 scanned reportSigns] at gate
      have hitList := signed_gate_recursive_iff_it_returns_the_nonempty_exact_positive_subsequence489.mp gate
      rw [positive_signs_of_g05_report_are_its_whole_original_ordered_hit_list489] at hitList
      have same := (recursive_report_keeps_the_whole_original_ordered_hit_list488 r hits priority).mpr hitList
      simp [routeFromCheckedG05Report488,checked,same]

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
