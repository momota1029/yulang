import Yulang.GeneralDeclarativeI65I74CoveredCandidateReification485
import Yulang.GeneralDeclarativeI65I74TypedRootSafety482

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint GuardedObservationInput)
open TypedRootSafety482 (AllRootSafe allRootCheckComplete requestRootCheck requestRootCheckSound)
open GeneralDeclarations (Declaration)

/-- This local priority slice is gated by every actual demanded root.
A failed root check does not pretend to classify the larger request. -/
def readAfterAllDemandedRoots486 {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (roots : List (Checkpoint n))
    (plans : List (List (CandidateVisitKey485 n))) (permit : Nat → CandidateVisitKey485 n → Bool)
    (packets : List (Nat × PlannedCandidateWire485 n)) : Option PreElection485 :=
  if requestRootCheck p pos rel roots then
    readPlannedPreElection485 p gd pos rel plans permit packets
  else none

theorem exact_whole_tape_uses_the_unaltered_safe_demanded_roots_before_candidate_priority486
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {roots : List (Checkpoint n)}
    {plans : List (List (CandidateVisitKey485 n))} {permit : Nat → CandidateVisitKey485 n → Bool}
    {packets : List (Nat × PlannedCandidateWire485 n)} {out : PreElection485}
    (got : readAfterAllDemandedRoots486 p gd pos rel roots plans permit packets = some out) :
    AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (·.lower))
      (roots.map Checkpoint.which) ∧
    readPlannedPreElection485 p gd pos rel plans permit packets = some out := by
  unfold readAfterAllDemandedRoots486 at got
  split at got
  · exact ⟨requestRootCheckSound _ _ _ _ (by assumption),got⟩
  · cases got

theorem original_candidate_plan_reifies_after_independently_safe_actual_demanded_roots486
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {which : List (Fin n)}
    {plans : List (List (CandidateVisitKey485 n))}
    {permit : Nat → CandidateVisitKey485 n → Bool} {Auth : Nat → CandidateVisitKey485 n → Prop}
    (root : AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (·.lower)) which)
    (guarded : ∀ i ∈ which, GuardedObservationInput p.old.state.core pos rel i)
    (recognizes : ∀ i key, Auth i key → permit i key = true)
    (allSchedules : plans.length = (visible485 p).length)
    (available : ∀ i : Fin (visible485 p).length, ∃ keys wires bits,
      plans[i.val]? = some keys ∧ ExactCandidateFootprint485 p gd pos rel i.val (Auth i) keys wires bits) :
    ∃ roots packets bits, roots.map Checkpoint.which = which ∧
      readAfterAllDemandedRoots486 p gd pos rel roots plans permit packets = some (gate485 bits) := by
  obtain ⟨roots,locations,old⟩ := allRootCheckComplete _ _ _ _ _ root guarded
  obtain ⟨packets,bits,_,found⟩ :=
    all_independently_planned_visible_candidates_have_one_finite_priority_tape485 recognizes allSchedules available
  exact ⟨roots,packets,bits,locations,by simp only [readAfterAllDemandedRoots486,requestRootCheck,old,ite_true,found]⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
