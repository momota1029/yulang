import Yulang.GeneralDeclarativeI65I74G05SignedMarks487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint)
open TypedRootSafety482 (requestRootCheck requestRootCheckSound AllRootSafe)
open GeneralDeclarations (Declaration)

theorem exact_original_g05_candidate_report_carries_evidence_for_every_fitting_model487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {Allowed : Nat → CandidateVisitKey485 n → Prop} {meaning : G05LocalMeaning487}
    {evidence : G05LocalEvidence487} {r : G05Report487 n}
    (exact : G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r)
    (agree : ∀ m : Model, FitsFull p.state m → ∀ i ord d v, meaning i ord d v → evidence m i ord d v) :
    G05HasOriginalModelEvidence487 p gd pos rel coords Allowed evidence r := by
  intro m fit i row d stored cell
  obtain ⟨r0,d0,there,located,_,mark⟩ := exact.2.2 i
  have eq := Option.some.inj (there.symm.trans stored)
  subst r0
  have same : d0 = d := congrArg Prod.snd (Option.some.inj
    (((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr located).symm.trans
      ((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr cell)))
  subst d0
  cases v : row.mark with
  | requiredCycle => rw [v] at mark; exact mark
  | nonrecursive vv => rw [v] at mark; exact agree m fit _ _ _ _ mark.2

theorem assembling_g05_report_preserves_complete_signed_scope_and_independent_local_verdicts487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {coords : List (Fin n)} {permit : Nat → CandidateVisitKey485 n → Bool} {check : G05LocalChecker487}
    {computed : List (ComputedOriginalCandidate486 n)}
    {signed : List (Nat × Bool)} {tokens : List (Option (List Nat))} {rows : List (G05CandidateRow487 n)}
    {tape : List (Nat × PlannedCandidateWire485 n)}
    (compiled : compileScopedRoster487 p gd pos rel palette coords permit = some computed)
    (verified : readTape485 p
      (readPlannedLocal485 p gd pos rel (computed.map ComputedOriginalCandidate486.keys)
        (permitAtOriginalVisibleSlot486 p permit)) tape = some signed)
    (assembled : readG05OrderedRows487 p check 0 computed signed tokens = some rows)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key)
    (meaning : G05LocalMeaning487)
    (localSound : ∀ i ord d w v, check i ord d w = some v → meaning i ord d v) :
    G05ExactCandidateReport487 p gd pos rel coords Allowed meaning ⟨rows,G05PriorityOfRows487 rows⟩ := by
  obtain ⟨signedLength,matched⟩ :=
    stored_g05_signed_bits_cover_the_same_independent_recursive_candidates487 compiled verified Allowed lawful
  obtain ⟨size,info⟩ := g05_ordered_rows_keep_the_entire_signed_candidate_roster487 assembled
  have allRows : rows.length = (visible485 p).length := size.trans signedLength
  refine ⟨rfl,allRows,?_⟩
  intro i
  have ok : i.val < rows.length := by rw [allRows]; exact i.isLt
  let row := rows[i.val]
  have stored : rows[i.val]? = some row := List.getElem?_eq_getElem ok
  obtain ⟨candidate,value,token,wasCandidate,wasBit,_,replayed⟩ := info i.val row stored
  have saw : readG05OneRow487 p check i.val candidate value token = some row := by
    simpa using replayed
  obtain ⟨d,cell,isBit,isOrdinal,sameKeys,_,markCheck⟩ :=
    new_g05_row_preserves_original_slot_signed_bit_observed_keys_and_actual_local_mark487 saw
  obtain ⟨c,_,onRoster,_,_,keys⟩ :=
    successful_scoped_roster_reads_every_actual_visible_slot_and_its_exact_independent_visits487
      compiled i Allowed lawful
  have same : candidate = c := Option.some.inj (wasCandidate.symm.trans onRoster)
  subst c
  obtain ⟨positiveOrdinal,_,bit,_,matchedBit,classification⟩ := matched i
  have sameSign : value = (positiveOrdinal,bit) := Option.some.inj (wasBit.symm.trans matchedBit)
  subst value
  refine ⟨row,d,stored,cell,?_,?_⟩
  · intro key
    rw [sameKeys,isOrdinal]
    constructor
    · intro has
      obtain ⟨root,arg,seen,head,path⟩ := (keys key).mp has
      exact ⟨arg,root,seen,head,path⟩
    · rintro ⟨arg,root,seen,head,path⟩
      exact (keys key).mpr ⟨root,arg,seen,head,path⟩
  · cases mark : row.mark with
    | requiredCycle =>
      rw [mark] at markCheck
      exact classification.mp (a_local_k2_mark_is_exactly_a_checked_true_bit_and_no_local_selection_token487.mp markCheck).1
    | nonrecursive v =>
      rw [mark] at markCheck
      obtain ⟨falseSign,w,_,result⟩ :=
        a_local_nonrecursive_mark_requires_a_real_local_receipt_not_failed_read487.mp markCheck
      exact ⟨fun cycle => Bool.false_ne_true (falseSign ▸ classification.mpr cycle),localSound _ _ _ _ _ result⟩

theorem new_g05_tag_is_sound_for_exact_prior_visits_and_the_supplied_local_meaning487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {check : G05LocalChecker487}
    {r : G05Report487 n} {w : G05FiniteWitness487 n}
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (meaning : G05LocalMeaning487) (localProtocol : G05ExactLocalProtocol487 check meaning)
    (evidence : G05LocalEvidence487)
    (modelSound : ∀ m : Model, FitsFull p.state m → ∀ i ord d v, meaning i ord d v → evidence m i ord d v)
    (accepted : checkFlatWithG05Tag487 p gd pos rel coords permit check (.inr r) (.inr w) = true) :
    w.roots.map Checkpoint.which = coords ∧
    G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r ∧
    G05HasOriginalModelEvidence487 p gd pos rel coords Allowed evidence r := by
  have ran := new_tag_check_succeeds_iff_it_replays_the_same_full_report_data487.mp accepted
  unfold readG05ScopedReport487 at ran
  split at ran
  · rename_i actualRoot
    obtain ⟨rootList,_⟩ := Bool.and_eq_true_iff.mp actualRoot
    let palette := computedOriginalPalette486 p.old.state.core pos rel
    cases compiled : compileScopedRoster487 p gd pos rel palette coords permit with
    | none => simp [palette,compiled,Option.bind] at ran
    | some computed =>
      let reader := readPlannedLocal485 p gd pos rel (computed.map ComputedOriginalCandidate486.keys)
        (permitAtOriginalVisibleSlot486 p permit)
      cases signed : readTape485 p reader w.tape with
      | none => simp [palette,compiled,reader,signed,Option.bind] at ran
      | some signs =>
        cases assembled : readG05OrderedRows487 p check 0 computed signs w.localTokens with
        | none => simp [palette,compiled,reader,signed,assembled,Option.bind] at ran
        | some rows =>
          have eq : (⟨rows,G05PriorityOfRows487 rows⟩ : G05Report487 n) = r := Option.some.inj
            (by simpa [palette,compiled,reader,signed,assembled,Option.bind] using ran)
          subst r
          have safe := assembling_g05_report_preserves_complete_signed_scope_and_independent_local_verdicts487
            compiled signed assembled Allowed scope.1 meaning localProtocol.1
          exact ⟨of_decide_eq_true rootList,safe,
            exact_original_g05_candidate_report_carries_evidence_for_every_fitting_model487 safe modelSound⟩
  · cases ran

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
