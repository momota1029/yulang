import Yulang.GeneralDeclarativeI65I74G05SemanticTransport488

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint GuardedObservationInput)
open TypedRootSafety482 (requestRootCheck requestRootCheckSound AllRootSafe)

theorem g05_checking_a_new_tag_never_substitutes_coordinates_for_the_actual_requested_roots488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    {r : G05Report487 n} {w : G05FiniteWitness487 n}
    (run : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inr w) = true) :
    w.roots.map Checkpoint.which = coords ∧ requestRootCheck p pos rel w.roots = true := by
  cases coords with
  | nil =>
    cases tried : readNoArgumentG05Report488 p gd pos rel permit test w with
    | none => simp [checkFlatWithDemandScopedG05Tag488,tried] at run
    | some output =>
      unfold readNoArgumentG05Report488 at tried
      split at tried
      · rename_i consumed
        obtain ⟨empty,checked⟩ := Bool.and_eq_true_iff.mp consumed
        have noRoots : w.roots = [] := List.isEmpty_iff.mp empty
        exact ⟨by simp [noRoots],checked⟩
      · cases tried
  | cons root rest =>
    cases tried : readG05ScopedReport487 p gd pos rel (root::rest) permit test w with
    | none => simp [checkFlatWithDemandScopedG05Tag488,checkFlatWithEquivalentG05Tag488,tried] at run
    | some output =>
      unfold readG05ScopedReport487 at tried
      split at tried
      · rename_i consumed
        obtain ⟨listEq,checked⟩ := Bool.and_eq_true_iff.mp consumed
        exact ⟨of_decide_eq_true listEq,checked⟩
      · cases tried

theorem original_root_read_back_is_sound_independently_of_the_prior_and_local_protocols488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    {r : G05Report487 n} {w : G05FiniteWitness487 n}
    (run : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inr w) = true) :
    w.roots.map Checkpoint.which = coords ∧
    AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (·.lower)) coords ∧
    coords.length = p.old.root.demand.arguments.length ∧
    ∀ root ∈ coords, GuardedObservationInput p.old.state.core pos rel root := by
  obtain ⟨same,scope⟩ := g05_checking_a_new_tag_never_substitutes_coordinates_for_the_actual_requested_roots488
    p gd pos rel coords permit test run
  have actual := requestRootCheckSound p pos rel w.roots scope
  obtain ⟨len,guards⟩ := all_checked_request_roots_carry_guards_and_exact_list_length487 scope
  have rootsLen : w.roots.length = p.old.root.demand.arguments.length := by
    simpa only [List.length_map] using len
  refine ⟨same,same ▸ actual,?_,same ▸ guards⟩
  rw [←same,List.length_map]
  exact rootsLen

theorem false_empty_coordinates_never_pass_for_a_nonempty_actual_demand488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (nonempty : p.old.root.demand.arguments ≠ [])
    (r : G05Report487 n) (w : G05FiniteWitness487 n) :
    checkFlatWithDemandScopedG05Tag488 p gd pos rel [] permit test (.inr r) (.inr w) = false := by
  cases h : checkFlatWithDemandScopedG05Tag488 p gd pos rel [] permit test (.inr r) (.inr w) with
  | false => rfl
  | true =>
    have scope := (original_root_read_back_is_sound_independently_of_the_prior_and_local_protocols488
      p gd pos rel [] permit test h).2.1
    exact False.elim (nonempty (empty_safe_coordinate_list_has_no_hidden_requested_lower488 scope))

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
