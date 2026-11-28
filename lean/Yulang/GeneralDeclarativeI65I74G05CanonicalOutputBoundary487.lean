import Yulang.GeneralDeclarativeI65I74G05CanonicalReification487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

theorem accepted_g05_report_observations_are_prescribed_by_the_canonical_generator487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {coords : List (Fin n)} {permit : Nat → CandidateVisitKey485 n → Bool}
    {probe : G05LocalChecker487} {report : G05Report487 n} {w : G05FiniteWitness487 n}
    (read : readG05ScopedReport487 p gd pos rel coords permit probe w = some report) :
    ∃ canonical : List (ComputedOriginalCandidate486 n),
      compileScopedRoster487 p gd pos rel (computedOriginalPalette486 p.old.state.core pos rel)
        coords permit = some canonical ∧
      ∀ (i : Nat) (row : G05CandidateRow487 n), report.rows[i]? = some row →
        ∃ c : ComputedOriginalCandidate486 n, canonical[i]? = some c ∧ row.observed = c.keys := by
  unfold readG05ScopedReport487 at read
  split at read
  · let palette := computedOriginalPalette486 p.old.state.core pos rel
    cases c : compileScopedRoster487 p gd pos rel palette coords permit with
    | none => simp [palette,c,Option.bind] at read
    | some canonical =>
      let reader := readPlannedLocal485 p gd pos rel (canonical.map ComputedOriginalCandidate486.keys)
        (permitAtOriginalVisibleSlot486 p permit)
      cases s : readTape485 p reader w.tape with
      | none => simp [palette,c,reader,s,Option.bind] at read
      | some signed =>
        cases a : readG05OrderedRows487 p probe 0 canonical signed w.localTokens with
        | none => simp [palette,c,reader,s,a,Option.bind] at read
        | some rows =>
          have same : (⟨rows,G05PriorityOfRows487 rows⟩ : G05Report487 n) = report := Option.some.inj
            (by simpa [palette,c,reader,s,a,Option.bind] using read)
          subst report
          refine ⟨canonical,rfl,?_⟩
          intro i row atIndex
          obtain ⟨stored,sign,token,atStored,_,_,run⟩ :=
            (g05_ordered_rows_keep_the_entire_signed_candidate_roster487 a).2 i row atIndex
          obtain ⟨_,_,_,_,keys,_,_⟩ := new_g05_row_preserves_original_slot_signed_bit_observed_keys_and_actual_local_mark487
            run
          exact ⟨stored,atStored,keys⟩
  · cases read

theorem same_inputs_cannot_accept_two_different_observed_serializations_on_the_same_row487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {coords : List (Fin n)} {permit : Nat → CandidateVisitKey485 n → Bool}
    {probe : G05LocalChecker487} {r s : G05Report487 n} {w1 w2 : G05FiniteWitness487 n}
    (first : checkFlatWithG05Tag487 p gd pos rel coords permit probe (.inr r) (.inr w1) = true)
    (second : checkFlatWithG05Tag487 p gd pos rel coords permit probe (.inr s) (.inr w2) = true)
    {i : Nat} {row1 row2 : G05CandidateRow487 n}
    (one : r.rows[i]? = some row1) (two : s.rows[i]? = some row2) :
    row1.observed = row2.observed := by
  obtain ⟨x,hx,rowsX⟩ := accepted_g05_report_observations_are_prescribed_by_the_canonical_generator487
    (new_tag_check_succeeds_iff_it_replays_the_same_full_report_data487.mp first)
  obtain ⟨y,hy,rowsY⟩ := accepted_g05_report_observations_are_prescribed_by_the_canonical_generator487
    (new_tag_check_succeeds_iff_it_replays_the_same_full_report_data487.mp second)
  have same : x = y := Option.some.inj (hx.symm.trans hy)
  subst y
  obtain ⟨a,aAt,eqA⟩ := rowsX i row1 one
  obtain ⟨b,bAt,eqB⟩ := rowsY i row2 two
  have eq : a = b := Option.some.inj (aAt.symm.trans bAt)
  subst b
  exact eqA.trans eqB.symm

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
