import Yulang.GeneralDeclarativeI65I74G05ScopedSignedRead489
import Yulang.GeneralDeclarativeI65I74G05Continuation488

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint GuardedObservationInput)
open TypedRootSafety482 (AllRootSafe)

/-- Compute a fresh complete finite preflight, pinned to the original
request coordinates. The callback supplying local verdicts is absent. -/
def readG05Preflight489 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (coords : List (Fin n)) (permit : Nat → CandidateVisitKey485 n → Bool) : Option PreElection485 := do
  let roots ← computedOriginalRootCertificates487 p.old.state.core pos rel
    (p.old.root.demand.arguments.map (·.lower))
  if roots.map Checkpoint.which = coords then
    readScopedPreElection487 p gd pos rel (computedOriginalPalette486 p.old.state.core pos rel) roots permit
  else none

theorem g05_preflight_has_the_actual_roots_and_independent_ordered_signs489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {out : PreElection485}
    (ran : readG05Preflight489 p gd pos rel coords permit = some out)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key) :
    AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (·.lower)) coords ∧
      ∃ bits, G05ExactSignedRoster489 p (IndependentScopedReturn487 p gd pos rel coords Allowed) bits ∧
        gate485 bits = out := by
  unfold readG05Preflight489 at ran
  cases h : computedOriginalRootCertificates487 p.old.state.core pos rel
      (p.old.root.demand.arguments.map (·.lower)) with
  | none => simp [h] at ran
  | some roots =>
    simp only [h,bind,Option.bind] at ran
    split at ran
    · rename_i own
      rw [←own]
      exact successful_scoped_g05_read_returns_exact_original_root_and_signed_roster489 ran Allowed lawful
    · cases ran

theorem original_nonempty_g05_demand_replays_full_preflight_without_any_local_receipts489
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (nonempty : coords ≠ []) :
    ∃ out, readG05Preflight489 p gd pos rel coords permit = some out := by
  have arity := registered_arity_for_each_visible_declaration_follows_from_any_actual_scoped_original_argument488
    scope nonempty
  obtain ⟨lawful,coherent,safe,guard,starts⟩ := scope
  obtain ⟨nodes,made,same⟩ := given_exact_old_guarded_safe_roots_the_computer_returns_all_in_same_order487 safe guard
  obtain ⟨bits,ran⟩ := independently_guarded_demand_and_prefix_authority_compile_checkable_automatic_tape487
    p gd pos rel coords permit Allowed (fun ord key yes => (lawful ord key).mp yes)
    safe guard arity starts coherent
  simp only [readAutomaticScopedPreElection487,made,bind,Option.bind] at ran
  refine ⟨gate485 bits,?_⟩
  simpa only [readG05Preflight489,made,bind,Option.bind,same,ite_true] using ran

/-- A positive preflight result is prior to local matching. In the other
cases the unchanged full verifier is still required to continue. -/
def routeG05PreflightThenChecked489 {n : Nat} {α : Type} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (coords : List (Fin n)) (permit : Nat → CandidateVisitKey485 n → Bool)
    (localCheck : G05LocalChecker487) (report : G05Report487 n) (wire : G05FiniteWitness487 n)
    (next : List (Nat × G05LocalVerdict487) → α) : G05Continuation488 α :=
  match readG05Preflight489 p gd pos rel coords permit with
  | some (.recursive hits) => .blockedByK2 hits
  | _ => routeFromCheckedG05Report488 p gd pos rel coords permit localCheck report wire next

theorem verified_g05_preflight_k2_preempts_even_missing_local_or_full_report_receipts489
    {n : Nat} {α : Type} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (hits : List Nat)
    (ran : readG05Preflight489 p gd pos rel coords permit = some (.recursive hits)) :
    ∀ (localCheck : G05LocalChecker487) (report : G05Report487 n) (wire : G05FiniteWitness487 n)
      (next : List (Nat × G05LocalVerdict487) → α),
      routeG05PreflightThenChecked489 p gd pos rel coords permit localCheck report wire next = .blockedByK2 hits := by
  intro localCheck report wire next
  simp [routeG05PreflightThenChecked489,ran]

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
