import Yulang.GeneralDeclarativeI65I74G05EmptyDemandSound488

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint)

private theorem visit_equivalent_g05_row_lists_are_reflexive488 {n : Nat}
    (rows : List (G05CandidateRow487 n)) :
    g05ReportRowsEquivalent488 rows rows = true := by
  apply indexed_ordinal_mark_and_visit_membership_reify_report_equivalence488 rfl
  intro i a b one two
  have eq : a = b := Option.some.inj (one.symm.trans two)
  subst b
  exact ⟨rfl,rfl,fun _ => Iff.rfl⟩

/-- The demand slice chooses how to reconstruct the finite tape. The
root replay still checks that this slice is the actual original demand. -/
def checkFlatWithDemandScopedG05Tag488 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (coords : List (Fin n)) (permit : Nat → CandidateVisitKey485 n → Bool)
    (test : G05LocalChecker487) (report : Sum Flat481.FlatReport (G05Report487 n))
    (wire : Sum Flat481.FlatWitness (G05FiniteWitness487 n)) : Bool :=
  match coords with
  | [] =>
    match report,wire with
    | .inl r,.inl w => Flat481.check_full_flat p r w
    | .inr r,.inr w =>
      match readNoArgumentG05Report488 p gd pos rel permit test w with
      | none => false
      | some canonical =>
        g05ReportRowsEquivalent488 canonical.rows r.rows && decide (r.priority = G05PriorityOfRows487 r.rows)
    | _,_ => false
  | _::_ => checkFlatWithEquivalentG05Tag488 p gd pos rel coords permit test report wire

theorem g05_coordinate_dispatch_keeps_every_old_tag_and_rejects_crossed_tags488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (old : Flat481.FlatReport) (input : Flat481.FlatWitness)
    (r : G05Report487 n) (w : G05FiniteWitness487 n) :
    checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inl old) (.inl input) =
      Flat481.check_full_flat p old input ∧
    checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inl old) (.inr w) = false ∧
    checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inl input) = false := by
  cases coords <;> exact ⟨rfl,rfl,rfl⟩

theorem verified_g05_report_has_exact_original_coordinates_and_evidence_for_all_fitting_models488
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {test : G05LocalChecker487}
    {r : G05Report487 n} {w : G05FiniteWitness487 n}
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (meaning : G05LocalMeaning487) (protocol : G05ExactLocalProtocol487 test meaning)
    (evidence : G05LocalEvidence487)
    (modelSound : ∀ m : Model, FitsFull p.state m → ∀ i ord d v, meaning i ord d v → evidence m i ord d v)
    (accept : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inr w) = true) :
    w.roots.map Checkpoint.which = coords ∧ G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r ∧
      G05HasOriginalModelEvidence487 p gd pos rel coords Allowed evidence r := by
  cases coords with
  | nil =>
    cases report : readNoArgumentG05Report488 p gd pos rel permit test w with
    | none => simp [checkFlatWithDemandScopedG05Tag488,report] at accept
    | some known =>
      have compares : (g05ReportRowsEquivalent488 known.rows r.rows &&
          decide (r.priority = G05PriorityOfRows487 r.rows)) = true := by
        simpa only [checkFlatWithDemandScopedG05Tag488,report] using accept
      obtain ⟨same,marked⟩ := Bool.and_eq_true_iff.mp compares
      obtain ⟨roots,independent⟩ :=
        no_argument_report_success_preserves_the_empty_original_scope_and_independent_classifications488
          p gd pos rel permit test Allowed meaning protocol report
      have resulting := g05_serialization_equivalence_preserves_the_independent_full_report488
        same (of_decide_eq_true marked) independent
      exact ⟨by simp [roots],resulting,
        exact_original_g05_candidate_report_carries_evidence_for_every_fitting_model487 resulting modelSound⟩
  | cons first rest =>
    exact g05_equivalent_tag_preserves_original_report_soundness_without_ordered_observation_equality488
      Allowed scope meaning protocol evidence modelSound accept

theorem independently_exact_g05_reports_reify_without_an_observation_order_or_arity_assumption488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (Allowed : Nat → CandidateVisitKey485 n → Prop) (meaning : G05LocalMeaning487)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (protocol : G05ExactLocalProtocol487 test meaning)
    (r : G05Report487 n) (report : G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r) :
    ∃ w : G05FiniteWitness487 n, w.roots.map Checkpoint.which = coords ∧
      checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inr w) = true := by
  cases coords with
  | nil =>
    obtain ⟨w,empty,proved⟩ := every_independent_zero_argument_report_reifies_without_an_arity_assumption488
      p gd pos rel permit test Allowed meaning scope protocol r report
    refine ⟨w,by simp [empty],?_⟩
    simp only [checkFlatWithDemandScopedG05Tag488,proved]
    exact Bool.and_eq_true_iff.mpr
      ⟨visit_equivalent_g05_row_lists_are_reflexive488 r.rows,decide_eq_true report.1⟩
  | cons first rest =>
    have arity := registered_arity_for_each_visible_declaration_follows_from_any_actual_scoped_original_argument488
      scope (by simp)
    exact each_independently_exact_noncanonical_g05_report_has_a_finite_equivalence_witness_under_actual_arity488
      p gd pos rel (first::rest) permit test Allowed meaning scope protocol arity r report

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
