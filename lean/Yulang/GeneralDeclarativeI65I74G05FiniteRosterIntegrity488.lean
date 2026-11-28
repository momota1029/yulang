import Yulang.GeneralDeclarativeI65I74G05RootScopeIntegrity488

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

private theorem assembled_local_receipts_have_exact_signed_length488
    {n : Nat} (p : FullProblem) (test : G05LocalChecker487) (offset : Nat)
    {compiled : List (ComputedOriginalCandidate486 n)} {signed : List (Nat × Bool)}
    {tokens : List (Option (List Nat))} {out : List (G05CandidateRow487 n)}
    (run : readG05OrderedRows487 p test offset compiled signed tokens = some out) :
    tokens.length = signed.length := by
  induction compiled generalizing offset signed tokens out with
  | nil =>
    cases signed <;> cases tokens <;> simp_all [readG05OrderedRows487]
  | cons c rest ih =>
    cases signed with
    | nil => simp [readG05OrderedRows487] at run
    | cons fact bits =>
      cases tokens with
      | nil => simp [readG05OrderedRows487] at run
      | cons receipt more =>
        cases one : readG05OneRow487 p test offset c fact receipt with
        | none => simp [readG05OrderedRows487,one] at run
        | some row =>
          cases next : readG05OrderedRows487 p test (offset+1) rest bits more with
          | none => simp [readG05OrderedRows487,one,next,Option.bind] at run
          | some other => exact congrArg Nat.succ (ih (offset+1) next)

private def G05RecheckedAssembly488 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (permit : Nat → CandidateVisitKey485 n → Bool)
    (test : G05LocalChecker487) (wire : G05FiniteWitness487 n) (normalized : G05Report487 n) : Prop :=
  ∃ (computed : List (ComputedOriginalCandidate486 n)) (bits : List (Nat × Bool)),
    readTape485 p (readPlannedLocal485 p gd pos rel (computed.map ComputedOriginalCandidate486.keys)
      (permitAtOriginalVisibleSlot486 p permit)) wire.tape = some bits ∧
    readG05OrderedRows487 p test 0 computed bits wire.localTokens = some normalized.rows

private theorem g05_readers_preserve_the_checkpoints_into_any_successful_assembled_report488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (wire : G05FiniteWitness487 n) (normalized : G05Report487 n)
    (go : Bool) (compile : Option (List (ComputedOriginalCandidate486 n)))
    (run : (if go then do
        let rows ← compile
        let signed ← readTape485 p
          (readPlannedLocal485 p gd pos rel (rows.map ComputedOriginalCandidate486.keys)
            (permitAtOriginalVisibleSlot486 p permit)) wire.tape
        let report ← readG05OrderedRows487 p test 0 rows signed wire.localTokens
        pure ⟨report,G05PriorityOfRows487 report⟩
      else none) = some normalized) :
    G05RecheckedAssembly488 p gd pos rel permit test wire normalized := by
  cases go
  · simp at run
  · cases source : compile with
    | none => simp [source] at run
    | some computed =>
      let read := readPlannedLocal485 p gd pos rel
        (computed.map ComputedOriginalCandidate486.keys) (permitAtOriginalVisibleSlot486 p permit)
      cases check : readTape485 p read wire.tape with
      | none => simp [source,read,check,Option.bind] at run
      | some signed =>
        cases out : readG05OrderedRows487 p test 0 computed signed wire.localTokens with
        | none => simp [source,read,check,out,Option.bind] at run
        | some rows =>
          have same : (⟨rows,G05PriorityOfRows487 rows⟩ : G05Report487 n) = normalized :=
            Option.some.inj (by simpa [source,read,check,out,Option.bind] using run)
          subst normalized
          exact ⟨computed,signed,check,out⟩

private theorem g05_acceptance_contains_an_independently_rechecked_finite_assembly488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    {report : G05Report487 n} {wire : G05FiniteWitness487 n}
    (valid : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr report) (.inr wire) = true) :
    ∃ normalized, G05RecheckedAssembly488 p gd pos rel permit test wire normalized ∧
      g05ReportRowsEquivalent488 normalized.rows report.rows = true := by
  cases coords with
  | nil =>
    cases ran : readNoArgumentG05Report488 p gd pos rel permit test wire with
    | none => simp [checkFlatWithDemandScopedG05Tag488,ran] at valid
    | some normalized =>
      refine ⟨normalized,?_,?_⟩
      · exact g05_readers_preserve_the_checkpoints_into_any_successful_assembled_report488
          p gd pos rel permit test wire normalized _ _ ran
      · exact (Bool.and_eq_true_iff.mp (by
          simpa only [checkFlatWithDemandScopedG05Tag488,ran] using valid)).1
  | cons first rest =>
    cases ran : readG05ScopedReport487 p gd pos rel (first::rest) permit test wire with
    | none => simp [checkFlatWithDemandScopedG05Tag488,checkFlatWithEquivalentG05Tag488,ran] at valid
    | some normalized =>
      refine ⟨normalized,?_,?_⟩
      · exact g05_readers_preserve_the_checkpoints_into_any_successful_assembled_report488
          p gd pos rel permit test wire normalized _ _ ran
      · exact (Bool.and_eq_true_iff.mp (by
          simpa only [checkFlatWithDemandScopedG05Tag488,checkFlatWithEquivalentG05Tag488,ran] using valid)).1

theorem g05_new_tag_cannot_drop_a_visible_candidate_a_tape_packet_or_a_local_token_slot488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    {report : G05Report487 n} {wire : G05FiniteWitness487 n}
    (valid : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr report) (.inr wire) = true) :
    report.rows.length = (visible485 p).length ∧
    wire.tape.length = (visible485 p).length ∧ wire.localTokens.length = (visible485 p).length ∧
    ∀ i : Fin (visible485 p).length, ∃ row decl,
      report.rows[i.val]? = some row ∧ OriginalRosterCell485 p i.val (row.ordinal,decl) := by
  obtain ⟨canonical,⟨compiled,bits,tape,assembly⟩,equivalent⟩ :=
    g05_acceptance_contains_an_independently_rechecked_finite_assembly488
      p gd pos rel coords permit test valid
  let read := readPlannedLocal485 p gd pos rel
    (compiled.map ComputedOriginalCandidate486.keys) (permitAtOriginalVisibleSlot486 p permit)
  let meaning : CandidateLocal (PlannedCandidateWire485 n) := fun k d w b => read k d w = some b
  have structured := (read_tape_reflects_the_actual_entire_visible_order485
    p read meaning (fun _ _ _ _ => Iff.rfl) wire.tape bits).mp tape
  obtain ⟨tLen,bLen,_⟩ := whole_tape_has_exact_visible_length_and_original_slot_order485 p meaning structured
  obtain ⟨cLen,steps⟩ := g05_ordered_rows_keep_the_entire_signed_candidate_roster487 assembly
  obtain ⟨rLen,eqRows⟩ := g05ReportRowsEquivalent_preserves_all_slots_and_individual_key_coverage488 equivalent
  have bitLen : bits.length = (visible485 p).length := by simpa only [List.length_range] using bLen
  have rowsLen := cLen.trans bitLen
  have packetLen : wire.tape.length = (visible485 p).length := by simpa only [List.length_range] using tLen
  have localLen := (assembled_local_receipts_have_exact_signed_length488 p test 0 assembly).trans bitLen
  refine ⟨rLen.symm.trans rowsLen,packetLen,localLen,?_⟩
  intro i
  have inRange : i.val < canonical.rows.length := rowsLen.symm ▸ i.isLt
  let actual := canonical.rows[i.val]
  have atSlot : canonical.rows[i.val]? = some actual := List.getElem?_eq_getElem inRange
  obtain ⟨external,atReport,sameOrd,_,_⟩ := eqRows i.val actual atSlot
  obtain ⟨candidate,sign,token,_,_,_,verified⟩ := steps i.val actual atSlot
  have ran : readG05OneRow487 p test i.val candidate sign token = some actual := by
    simpa only [Nat.zero_add] using verified
  obtain ⟨d,origin,_,_,_,_,_⟩ := new_g05_row_preserves_original_slot_signed_bit_observed_keys_and_actual_local_mark487 ran
  exact ⟨external,d,atReport,sameOrd ▸ origin⟩

theorem g05_report_marks_depend_on_exact_local_tokens_not_default_classifications488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    {report : G05Report487 n} {wire : G05FiniteWitness487 n}
    (valid : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr report) (.inr wire) = true) :
    ∀ i : Fin (visible485 p).length, ∃ row decl token,
      report.rows[i.val]? = some row ∧ OriginalRosterCell485 p i.val (row.ordinal,decl) ∧
      wire.localTokens[i.val]? = some token ∧
      match row.mark with
      | .requiredCycle => token = none
      | .nonrecursive v => ∃ data, token = some data ∧ test i.val row.ordinal decl data = some v := by
  obtain ⟨canonical,⟨compiled,bits,tape,assembly⟩,equivalent⟩ :=
    g05_acceptance_contains_an_independently_rechecked_finite_assembly488 p gd pos rel coords permit test valid
  let reader := readPlannedLocal485 p gd pos rel
    (compiled.map ComputedOriginalCandidate486.keys) (permitAtOriginalVisibleSlot486 p permit)
  let meaning : CandidateLocal (PlannedCandidateWire485 n) := fun k d w b => reader k d w = some b
  have structured := (read_tape_reflects_the_actual_entire_visible_order485
    p reader meaning (fun _ _ _ _ => Iff.rfl) wire.tape bits).mp tape
  have signedLen := (whole_tape_has_exact_visible_length_and_original_slot_order485 p meaning structured).2.1
  obtain ⟨cLen,rechecked⟩ := g05_ordered_rows_keep_the_entire_signed_candidate_roster487 assembly
  obtain ⟨_,eqRows⟩ := g05ReportRowsEquivalent_preserves_all_slots_and_individual_key_coverage488 equivalent
  have total : canonical.rows.length = (visible485 p).length := by
    simpa only [List.length_range] using cLen.trans signedLen
  intro i
  let old := canonical.rows[i.val]'(total.symm ▸ i.isLt)
  have atOld : canonical.rows[i.val]? = some old := List.getElem?_eq_getElem (total.symm ▸ i.isLt)
  obtain ⟨reportRow,atReport,ord,state,_⟩ := eqRows i.val old atOld
  obtain ⟨row,signed,token,_,_,atToken,first⟩ := rechecked i.val old atOld
  have accept : readG05OneRow487 p test i.val row signed token = some old := by
    simpa only [Nat.zero_add] using first
  obtain ⟨d,origin,_,_,_,_,code⟩ :=
    new_g05_row_preserves_original_slot_signed_bit_observed_keys_and_actual_local_mark487 accept
  refine ⟨reportRow,d,token,atReport,ord ▸ origin,atToken,?_⟩
  rw [state,ord] at code
  cases mark : reportRow.mark with
  | requiredCycle =>
    rw [mark] at code
    exact (a_local_k2_mark_is_exactly_a_checked_true_bit_and_no_local_selection_token487.mp code).2
  | nonrecursive v =>
    rw [mark] at code
    exact (a_local_nonrecursive_mark_requires_a_real_local_receipt_not_failed_read487.mp code).2

theorem a_missing_local_token_cannot_force_a_nonrecursive_candidate_mark488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (r : G05Report487 n) (w : G05FiniteWitness487 n)
    (i : Fin (visible485 p).length) (row : G05CandidateRow487 n) (v : G05LocalVerdict487)
    (atRow : r.rows[i.val]? = some row) (nonrecursive : row.mark = .nonrecursive v)
    (absent : w.localTokens[i.val]? = some none) :
    checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inr w) = false := by
  cases checked : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inr w) with
  | false => rfl
  | true =>
    obtain ⟨real,d,data,atReal,_,atData,matched⟩ :=
      g05_report_marks_depend_on_exact_local_tokens_not_default_classifications488 p gd pos rel coords permit test checked i
    have eqRow := Option.some.inj (atReal.symm.trans atRow)
    subst real
    have missing := Option.some.inj (atData.symm.trans absent)
    subst data
    rw [nonrecursive] at matched
    obtain ⟨_,impossible,_⟩ := matched
    cases impossible

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
