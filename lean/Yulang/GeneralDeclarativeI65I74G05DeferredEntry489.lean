import Yulang.GeneralDeclarativeI65I74G05K2BeforeLocal489

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

/-- Construction of the full report and local receipts is deferred.
The positive preflight branch does not request either of them. -/
def routeG05WithDeferredLocal489 {n : Nat} {α : Type} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (coords : List (Fin n)) (permit : Nat → CandidateVisitKey485 n → Bool)
    (check : G05LocalChecker487) (supply : Unit → Option (G05Report487 n × G05FiniteWitness487 n))
    (next : List (Nat × G05LocalVerdict487) → α) : G05Continuation488 α :=
  match readG05Preflight489 p gd pos rel coords permit with
  | some (.recursive hits) => .blockedByK2 hits
  | _ =>
    match supply () with
    | none => .notReplayed
    | some (report,wire) => routeFromCheckedG05Report488 p gd pos rel coords permit check report wire next

theorem deferred_g05_route_is_equal_to_eager_route_when_full_input_is_already_supplied489
    {n : Nat} {α : Type} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool)
    (test : G05LocalChecker487) (r : G05Report487 n) (w : G05FiniteWitness487 n)
    (supply : Unit → Option (G05Report487 n × G05FiniteWitness487 n))
    (givenFull : supply () = some (r,w))
    (next : List (Nat × G05LocalVerdict487) → α) :
    routeG05WithDeferredLocal489 p gd pos rel coords permit test supply next =
      routeG05PreflightThenChecked489 p gd pos rel coords permit test r w next := by
  unfold routeG05WithDeferredLocal489 routeG05PreflightThenChecked489
  cases h : readG05Preflight489 p gd pos rel coords permit with
  | none => simp [givenFull]
  | some out => cases out <;> simp [givenFull]

theorem a_positive_g05_preflight_needs_neither_a_local_checker_nor_a_full_report_supplier489
    {n : Nat} {α : Type} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {hits : List Nat}
    (scan : readG05Preflight489 p gd pos rel coords permit = some (.recursive hits)) :
    ∀ (test : G05LocalChecker487) (supply : Unit → Option (G05Report487 n × G05FiniteWitness487 n))
      (next : List (Nat × G05LocalVerdict487) → α),
      routeG05WithDeferredLocal489 p gd pos rel coords permit test supply next = .blockedByK2 hits := by
  intro test supply next
  simp [routeG05WithDeferredLocal489,scan]

theorem g05_deferred_route_without_full_receipts_distinguishes_positive_preflight_from_failure489
    {n : Nat} {α : Type} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (supply : Unit → Option (G05Report487 n × G05FiniteWitness487 n))
    (missing : supply () = none) (next : List (Nat × G05LocalVerdict487) → α) :
    let result := routeG05WithDeferredLocal489 p gd pos rel coords permit test supply next
    (result = .notReplayed ↔ ∀ hits, readG05Preflight489 p gd pos rel coords permit ≠ some (.recursive hits)) ∧
    ∀ hits, result = .blockedByK2 hits ↔ readG05Preflight489 p gd pos rel coords permit = some (.recursive hits) := by
  dsimp only
  unfold routeG05WithDeferredLocal489
  cases ran : readG05Preflight489 p gd pos rel coords permit with
  | none => simp [missing]
  | some out =>
    cases out with
    | allSafe ords => simp [missing]
    | recursive hits => simp

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
