import Yulang.GeneralDeclarativeI65I74G05CanonicalOutputBoundary487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

def duplicateEachObservationList487 {n : Nat} (r : G05Report487 n) : G05Report487 n :=
  { r with rows := r.rows.map fun row => { row with observed := row.observed ++ row.observed } }

theorem independent_g05_exactness_currently_does_not_fix_observation_multiplicity487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {Allowed : Nat → CandidateVisitKey485 n → Prop} {meaning : G05LocalMeaning487}
    {r : G05Report487 n}
    (exact : G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r) :
    G05ExactCandidateReport487 p gd pos rel coords Allowed meaning (duplicateEachObservationList487 r) := by
  refine ⟨?_,?_,?_⟩
  · have eq : G05PriorityOfRows487 (duplicateEachObservationList487 r).rows = G05PriorityOfRows487 r.rows := by
      simp [duplicateEachObservationList487,G05PriorityOfRows487,List.filterMap_map,Function.comp_def]
    exact exact.1.trans eq.symm
  · simpa [duplicateEachObservationList487] using exact.2.1
  · intro i
    obtain ⟨row,d,atSlot,source,visits,mark⟩ := exact.2.2 i
    let doubled : G05CandidateRow487 n := {row with observed := row.observed ++ row.observed}
    have next : (duplicateEachObservationList487 r).rows[i.val]? = some doubled := by
      simp [duplicateEachObservationList487,List.getElem?_map,atSlot,doubled]
    refine ⟨doubled,d,next,source,?_,mark⟩
    intro key
    change key ∈ row.observed ++ row.observed ↔ _
    simpa only [List.mem_append,or_self] using visits key

theorem canonical_g05_tag_refuses_a_nonempty_doubled_serialization_for_every_witness487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {coords : List (Fin n)} {permit : Nat → CandidateVisitKey485 n → Bool}
    {probe : G05LocalChecker487} {r : G05Report487 n} {w : G05FiniteWitness487 n}
    (accepted : checkFlatWithG05Tag487 p gd pos rel coords permit probe (.inr r) (.inr w) = true)
    {i : Nat} {row : G05CandidateRow487 n} (located : r.rows[i]? = some row)
    (nonempty : row.observed ≠ []) (other : G05FiniteWitness487 n) :
    checkFlatWithG05Tag487 p gd pos rel coords permit probe (.inr (duplicateEachObservationList487 r))
      (.inr other) = false := by
  cases attempted : checkFlatWithG05Tag487 p gd pos rel coords permit probe
      (.inr (duplicateEachObservationList487 r)) (.inr other) with
  | false => rfl
  | true =>
    let doubled : G05CandidateRow487 n := {row with observed := row.observed ++ row.observed}
    have there : (duplicateEachObservationList487 r).rows[i]? = some doubled := by
      simp [duplicateEachObservationList487,List.getElem?_map,located,doubled]
    have forced := same_inputs_cannot_accept_two_different_observed_serializations_on_the_same_row487
      accepted attempted located there
    have size : row.observed.length = row.observed.length + row.observed.length := by
      simpa [doubled,List.length_append] using congrArg List.length forced
    have positive : 0 < row.observed.length := List.length_pos_iff.mpr nonempty
    omega

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
