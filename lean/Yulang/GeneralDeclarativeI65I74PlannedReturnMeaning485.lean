import Yulang.GeneralDeclarativeI65I74PlannedPreElection485

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions graphOf)
open QuotientObservation471 (ReturnsUpToEquality)
open Producer479 (Site Trail)

private theorem exact_trail_terminal_is_its_last_existing_coordinate
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {first last : Site s pos} {moves points bit}
    (path : Trail s pos rel first moves points last bit) :
    (first.index::points).getLast? = some last.index := by
  induction path with
  | stop => rfl
  | step _ _ _ _ ih => simpa only [List.getLast?_cons_cons] using ih

theorem guarded_candidate_path_checks_the_exact_sign_of_its_key_terminal485
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {i w}
    (path : CandidatePath485 p gd pos rel i w) :
    (candidateVisitKey485 w).points.getLast? = some path.last.index ∧
    (path.terminalBit = true ↔ ReturnsUpToEquality (graphOf p.old.state.core pos) path.last.index) := by
  refine ⟨?_,(Producer479.declarative_trail_reads_existing_edges_and_returns_at_the_terminal479 path.visited).2⟩
  unfold candidateVisitKey485
  simp only [path.originalCursor]
  exact exact_trail_terminal_is_its_last_existing_coordinate path.visited

def RecurringPlannedVisit485 {n : Nat} (s : GeneralDeclarativeI65.State) (pos : Positions n)
    (keys : List (CandidateVisitKey485 n)) : Prop :=
  ∃ key ∈ keys, ∃ j, key.points.getLast? = some j ∧ ReturnsUpToEquality (graphOf s pos) j

theorem signed_footprint_accepts_positive_exactly_for_a_recursive_planned_visit485
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {i : Nat}
    {Auth : CandidateVisitKey485 n → Prop} {keys wires bits}
    (exact : ExactCandidateFootprint485 p gd pos rel i Auth keys wires bits) :
    bits.any id = true ↔ RecurringPlannedVisit485 p.old.state.core pos keys := by
  induction exact with
  | nil => simp [RecurringPlannedVisit485]
  | cons path auth proper rest ih =>
    have sign := guarded_candidate_path_checks_the_exact_sign_of_its_key_terminal485 path
    simp only [List.any_cons,id_eq,Bool.or_eq_true,ih]
    constructor
    · rintro (first|⟨key,here,j,terminal,cycle⟩)
      · exact ⟨_,List.mem_cons_self ..,_,sign.1,sign.2.mp first⟩
      · exact ⟨key,List.mem_cons_of_mem _ here,j,terminal,cycle⟩
    · rintro ⟨key,atList,j,endpoint,cycle⟩
      rcases List.mem_cons.mp atList with atHead|atTail
      · subst key
        have same := Option.some.inj (endpoint.symm.trans sign.1)
        exact .inl (sign.2.mpr (same ▸ cycle))
      · exact .inr ⟨key,atTail,j,endpoint,cycle⟩

/-- This covers an independent candidate-local recursive judgement only
when its actual visits are covered by the authorised stored plan. The
sign of one sampled route is not a statement about other routes. -/
theorem globally_meaningful_local_negative_requires_independent_coverage485
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {i : Nat}
    {Auth : CandidateVisitKey485 n → Prop} {keys wires bits}
    (exact : ExactCandidateFootprint485 p gd pos rel i Auth keys wires bits)
    (actualRecurs : Prop)
    (coverage : actualRecurs → RecurringPlannedVisit485 p.old.state.core pos keys)
    (safe : bits.any id = false) :
    ¬ actualRecurs := by
  intro actual
  have contradiction := (signed_footprint_accepts_positive_exactly_for_a_recursive_planned_visit485 exact).mpr
    (coverage actual)
  rw [safe] at contradiction
  cases contradiction

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
