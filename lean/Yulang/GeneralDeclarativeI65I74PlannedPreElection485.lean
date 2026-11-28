import Yulang.GeneralDeclarativeI65I74CandidateVisitFootprint485
import Yulang.GeneralDeclarativeI65I74ElectionAfterTape485
import Yulang.GeneralDeclarativeI65I72GroundedRawOrder405

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open GeneralDeclarations (Declaration)

structure PlannedCandidateWire485 (n : Nat) where
  visibleOrdinal : Nat
  paths : List (CandidatePathWire485 n)

theorem two_visible_slots_cannot_claim_one_original_registry_ordinal485
    (p : FullProblem) {i j ord : Nat} {d e : Declaration}
    (left : OriginalRosterCell485 p i (ord,d)) (right : OriginalRosterCell485 p j (ord,e)) :
    i = j := by
  rcases Nat.lt_trichotomy i j with h|h|h
  · exact False.elim (Nat.lt_irrefl _ (unfilter_keeps_original_order405
      (role485 p) (declared485 p) h left.2.1 right.2.1))
  · exact h
  · exact False.elim (Nat.lt_irrefl _ (unfilter_keeps_original_order405
      (role485 p) (declared485 p) h right.2.1 left.2.1))

/-- The phase supplies a plan independently of the packet. The finite
packet must visit each of its exact physical source positions in order. -/
def readPlannedLocal485 {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n))
    (plans : List (List (CandidateVisitKey485 n))) (permit : Nat → CandidateVisitKey485 n → Bool) :
    CandidateCheck (PlannedCandidateWire485 n) :=
  fun ord d packet => do
    let (physical,decl) ← rosterCell485 p packet.visibleOrdinal
    if physical = ord ∧ decl = d then
      let required ← plans[packet.visibleOrdinal]?
      let bits ← readCandidateFootprint485 p gd pos rel packet.visibleOrdinal
        (permit packet.visibleOrdinal) required packet.paths
      pure (bits.any id)
    else none

def readPlannedPreElection485 {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n))
    (plans : List (List (CandidateVisitKey485 n))) (permit : Nat → CandidateVisitKey485 n → Bool)
    (packets : List (Nat × PlannedCandidateWire485 n)) : Option PreElection485 :=
  if plans.length = (visible485 p).length then
    beforeElection485 p (readPlannedLocal485 p gd pos rel plans permit) packets
  else none

theorem finite_local_tape_result_preserves_the_original_authorized_signed_footprint485
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {plans : List (List (CandidateVisitKey485 n))}
    {permit : Nat → CandidateVisitKey485 n → Bool} (Authorized : Nat → CandidateVisitKey485 n → Prop)
    (permitSound : ∀ i key, permit i key = true → Authorized i key)
    {ord : Nat} {d : Declaration} {packet : PlannedCandidateWire485 n} {sign : Bool}
    (ran : readPlannedLocal485 p gd pos rel plans permit ord d packet = some sign) :
    OriginalRosterCell485 p packet.visibleOrdinal (ord,d) ∧
    ∃ keys bits, plans[packet.visibleOrdinal]? = some keys ∧
      ExactCandidateFootprint485 p gd pos rel packet.visibleOrdinal
        (Authorized packet.visibleOrdinal) keys packet.paths bits ∧
      bits.any id = sign := by
  unfold readPlannedLocal485 at ran
  cases h : rosterCell485 p packet.visibleOrdinal with
  | none => simp [h] at ran
  | some stored =>
    rcases stored with ⟨found,decl⟩
    simp only [h,bind,Option.bind] at ran
    split at ran
    · rename_i visible
      obtain ⟨rfl,rfl⟩ := visible
      refine ⟨(roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mp h,?_⟩
      cases grid : plans[packet.visibleOrdinal]? with
      | none => simp [grid] at ran
      | some keys =>
        cases found : readCandidateFootprint485 p gd pos rel packet.visibleOrdinal
            (permit packet.visibleOrdinal) keys packet.paths with
        | none => simp [grid,found] at ran
        | some bits =>
          exact ⟨keys,bits,rfl,finite_candidate_footprint_reflects_each_exact_permitted_visit485
            p gd pos rel packet.visibleOrdinal _ _ (permitSound _) _ _ _ found,
            Option.some.inj (by simpa [grid,found] using ran)⟩
    · cases ran

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
