import Yulang.GeneralDeclarativeI65I74G05ExactReportUniqueness488

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint)

theorem exact_g05_acceptance_can_transport_between_protocol_encodings_of_the_same_source488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (leftPermit rightPermit : Nat → CandidateVisitKey485 n → Bool)
    (leftCheck rightCheck : G05LocalChecker487)
    (Allowed : Nat → CandidateVisitKey485 n → Prop) (meaning : G05LocalMeaning487)
    (leftScope : G05ExactVisitInputs487 p gd pos rel coords leftPermit Allowed)
    (rightScope : G05ExactVisitInputs487 p gd pos rel coords rightPermit Allowed)
    (leftProtocol : G05ExactLocalProtocol487 leftCheck meaning)
    (rightProtocol : G05ExactLocalProtocol487 rightCheck meaning)
    (report : G05Report487 n) :
    (∃ w : G05FiniteWitness487 n, w.roots.map Checkpoint.which = coords ∧
      checkFlatWithDemandScopedG05Tag488 p gd pos rel coords leftPermit leftCheck (.inr report) (.inr w) = true) ↔
    (∃ w : G05FiniteWitness487 n, w.roots.map Checkpoint.which = coords ∧
      checkFlatWithDemandScopedG05Tag488 p gd pos rel coords rightPermit rightCheck (.inr report) (.inr w) = true) := by
  have compare (emit read : Nat → CandidateVisitKey485 n → Bool)
      (build decode : G05LocalChecker487)
      (one : G05ExactVisitInputs487 p gd pos rel coords emit Allowed)
      (two : G05ExactVisitInputs487 p gd pos rel coords read Allowed)
      (encodes : G05ExactLocalProtocol487 build meaning)
      (decodes : G05ExactLocalProtocol487 decode meaning)
      (w : G05FiniteWitness487 n)
      (input : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords emit build (.inr report) (.inr w) = true) :
      ∃ w' : G05FiniteWitness487 n, w'.roots.map Checkpoint.which = coords ∧
        checkFlatWithDemandScopedG05Tag488 p gd pos rel coords read decode (.inr report) (.inr w') = true := by
    have semantic := (verified_g05_report_has_exact_original_coordinates_and_evidence_for_all_fitting_models488
      Allowed one meaning encodes (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ _ => True.intro) input).2.1
    exact independently_exact_g05_reports_reify_without_an_observation_order_or_arity_assumption488
      p gd pos rel coords read decode Allowed meaning two decodes report semantic
  constructor
  · rintro ⟨w,_,yes⟩
    exact compare _ _ _ _ leftScope rightScope leftProtocol rightProtocol w yes
  · rintro ⟨w,_,yes⟩
    exact compare _ _ _ _ rightScope leftScope rightProtocol leftProtocol w yes

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
