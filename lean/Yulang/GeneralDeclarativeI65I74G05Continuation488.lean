import Yulang.GeneralDeclarativeI65I74G05FiniteRosterIntegrity488

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

inductive G05Continuation488 (α : Type) where
  | notReplayed
  | blockedByK2 (originalOrdinals : List Nat)
  | continued (value : α)

/-- The next phase is a parameter, not an election rule. It receives the
checked ordered local marks, including unresolved marks. -/
def routeFromCheckedG05Report488 {n : Nat} {α : Type} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (coords : List (Fin n)) (permit : Nat → CandidateVisitKey485 n → Bool)
    (test : G05LocalChecker487) (r : G05Report487 n) (w : G05FiniteWitness487 n)
    (next : List (Nat × G05LocalVerdict487) → α) : G05Continuation488 α :=
  if checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inr w) then
    match r.priority with
    | .recursive ords => .blockedByK2 ords
    | .eligible marks => .continued (next marks)
  else .notReplayed

theorem an_unverified_g05_report_never_routes_to_election_or_reports_a_language_rejection488
    {n : Nat} {α : Type} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {test : G05LocalChecker487}
    {r : G05Report487 n} {w : G05FiniteWitness487 n}
    (failed : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inr w) = false)
    (next : List (Nat × G05LocalVerdict487) → α) :
    routeFromCheckedG05Report488 p gd pos rel coords permit test r w next = .notReplayed := by
  simp [routeFromCheckedG05Report488,failed]

theorem a_real_original_k2_cycle_preempts_every_next_phase_on_a_verified_g05_report488
    {n : Nat} {α : Type} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (Allowed : Nat → CandidateVisitKey485 n → Prop) (meaning : G05LocalMeaning487)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (protocol : G05ExactLocalProtocol487 test meaning)
    (r : G05Report487 n) (w : G05FiniteWitness487 n)
    (accepted : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inr w) = true)
    (i : Fin (visible485 p).length) (cyclic : IndependentScopedReturn487 p gd pos rel coords Allowed i) :
    ∃ hits, hits = reportedOriginalG05Cycles488 r.rows ∧ hits ≠ [] ∧
      (∀ next : List (Nat × G05LocalVerdict487) → α,
        routeFromCheckedG05Report488 p gd pos rel coords permit test r w next = .blockedByK2 hits) := by
  have sound := (verified_g05_report_has_exact_original_coordinates_and_evidence_for_all_fitting_models488
    Allowed scope meaning protocol (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ _ => True.intro) accepted).2.1
  cases status : r.priority with
  | eligible marks => exact False.elim (eligible_report_excludes_every_independently_visited_k2_cycle488 sound status i cyclic)
  | recursive hits =>
    obtain ⟨ex,positive⟩ := (recursive_report_keeps_the_whole_original_ordered_hit_list488 r hits sound.1).mp status
    exact ⟨hits,ex,positive,fun next => by simp [routeFromCheckedG05Report488,accepted,status]⟩

theorem continuation_of_a_verified_g05_report_keeps_the_exact_ordered_marks488
    {n : Nat} {α : Type} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {test : G05LocalChecker487}
    {r : G05Report487 n} {w : G05FiniteWitness487 n}
    {marks : List (Nat × G05LocalVerdict487)}
    (accepted : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inr w) = true)
    (eligible : r.priority = .eligible marks) (next : List (Nat × G05LocalVerdict487) → α) :
    routeFromCheckedG05Report488 p gd pos rel coords permit test r w next = .continued (next marks) := by
  simp [routeFromCheckedG05Report488,accepted,eligible]

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
