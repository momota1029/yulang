import Yulang.GeneralDeclarativeI65I74G05EmptyDemandReification488

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open GeneralDeclarations (Declaration)

private theorem checked_empty_scope_local_tape_has_no_positive_bit488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool)
    (computed : List (ComputedOriginalCandidate486 n))
    (every : ∀ i : Fin (visible485 p).length, ∃ d ord,
      OriginalRosterCell485 p i.val (ord,d) ∧ computed[i.val]? = some ⟨ord,[],⟨i.val,[]⟩⟩)
    {ord : Nat} {d : Declaration} {wire : PlannedCandidateWire485 n} {sign : Bool}
    (ok : readPlannedLocal485 p gd pos rel (computed.map ComputedOriginalCandidate486.keys)
      (permitAtOriginalVisibleSlot486 p permit) ord d wire = some sign) : sign = false := by
  obtain ⟨scope,keys,bits,atKeys,actual,bit⟩ :=
    finite_local_tape_result_preserves_the_original_authorized_signed_footprint485
      (fun _ _ => True) (fun _ _ _ => True.intro) ok
  have bound : wire.visibleOrdinal < (visible485 p).length := (List.getElem?_eq_some_iff.mp scope.1).1
  obtain ⟨_,_,_,rowAt⟩ := every ⟨wire.visibleOrdinal,bound⟩
  have empty : (computed.map ComputedOriginalCandidate486.keys)[wire.visibleOrdinal]? = some [] := by
    simp [List.getElem?_map,rowAt]
  have same : keys = [] := Option.some.inj (atKeys.symm.trans empty)
  subst keys
  generalize emptyPaths : wire.paths = paths at actual
  cases actual
  exact bit.symm

private theorem empty_demand_checked_signs_keep_only_original_ordinals488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool)
    (computed : List (ComputedOriginalCandidate486 n))
    (every : ∀ i : Fin (visible485 p).length, ∃ d ord,
      OriginalRosterCell485 p i.val (ord,d) ∧ computed[i.val]? = some ⟨ord,[],⟨i.val,[]⟩⟩)
    {wires : List (Nat × PlannedCandidateWire485 n)} {bits : List (Nat × Bool)}
    (ok : readTape485 p (readPlannedLocal485 p gd pos rel
      (computed.map ComputedOriginalCandidate486.keys) (permitAtOriginalVisibleSlot486 p permit)) wires =
        some bits) :
    bits.length = (visible485 p).length ∧
    ∀ i : Fin (visible485 p).length, ∃ d ord,
      OriginalRosterCell485 p i.val (ord,d) ∧ bits[i.val]? = some (ord,false) := by
  let reader := readPlannedLocal485 p gd pos rel
    (computed.map ComputedOriginalCandidate486.keys) (permitAtOriginalVisibleSlot486 p permit)
  let meaning : CandidateLocal (PlannedCandidateWire485 n) := fun k d w b => reader k d w = some b
  have tape := (read_tape_reflects_the_actual_entire_visible_order485
    p reader meaning (fun _ _ _ _ => Iff.rfl) wires bits).mp ok
  obtain ⟨wireLen,bitLen,indexed⟩ := whole_tape_has_exact_visible_length_and_original_slot_order485 p meaning tape
  refine ⟨by simpa only [List.length_range] using bitLen,?_⟩
  intro i
  have within : i.val < wires.length := by simpa only [wireLen,List.length_range] using i.isLt
  let w := wires[i.val]
  have atW : wires[i.val]? = some w := List.getElem?_eq_getElem within
  have atSlot : ((List.range (visible485 p).length).zip wires)[i.val]? = some (i.val,w) :=
    List.getElem?_zip_eq_some.mpr ⟨List.getElem?_range i.isLt,atW⟩
  obtain ⟨d,b,cell,mark,atBit⟩ := indexed i.val _ atSlot
  have no := checked_empty_scope_local_tape_has_no_positive_bit488 p gd pos rel permit computed every mark
  exact ⟨d,w.1,cell,no ▸ atBit⟩

theorem no_argument_report_success_preserves_the_empty_original_scope_and_independent_classifications488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (test : G05LocalChecker487)
    (Allowed : Nat → CandidateVisitKey485 n → Prop) (meaning : G05LocalMeaning487)
    (protocol : G05ExactLocalProtocol487 test meaning)
    {wire : G05FiniteWitness487 n} {r : G05Report487 n}
    (run : readNoArgumentG05Report488 p gd pos rel permit test wire = some r) :
    wire.roots = [] ∧ G05ExactCandidateReport487 p gd pos rel [] Allowed meaning r := by
  obtain ⟨computed,compiled,_,_,every⟩ :=
    zero_demand_arg_roster_generates_exactly_one_empty_wire_per_visible_slot488 p gd pos rel permit
  unfold readNoArgumentG05Report488 at run
  split at run
  · rename_i eligible
    have empty : wire.roots = [] := List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp eligible).1
    let reader := readPlannedLocal485 p gd pos rel
      (computed.map ComputedOriginalCandidate486.keys) (permitAtOriginalVisibleSlot486 p permit)
    cases replay : readTape485 p reader wire.tape with
    | none => simp [compiled,reader,replay,Option.bind] at run
    | some signed =>
      cases assemble : readG05OrderedRows487 p test 0 computed signed wire.localTokens with
      | none => simp [compiled,reader,replay,assemble,Option.bind] at run
      | some rows =>
        have exact : (⟨rows,G05PriorityOfRows487 rows⟩ : G05Report487 n) = r :=
          Option.some.inj (by simpa [compiled,reader,replay,assemble,Option.bind] using run)
        subst r
        obtain ⟨signedLen,zero⟩ :=
          empty_demand_checked_signs_keep_only_original_ordinals488 p gd pos rel permit computed every replay
        obtain ⟨rowLen,indexed⟩ := g05_ordered_rows_keep_the_entire_signed_candidate_roster487 assemble
        have count := rowLen.trans signedLen
        refine ⟨empty,rfl,count,?_⟩
        intro i
        have bound : i.val < rows.length := by rw [count]; exact i.isLt
        let row := rows[i.val]
        have atRow : rows[i.val]? = some row := List.getElem?_eq_getElem bound
        obtain ⟨candidate,mark,receipt,actual,atMark,_,ran⟩ := indexed i.val row atRow
        obtain ⟨_,originOrdinal,_,origin⟩ := every i
        have candidateEq := Option.some.inj (actual.symm.trans origin)
        subst candidate
        obtain ⟨_,signedOrdinal,_,known⟩ := zero i
        have markEq := Option.some.inj (atMark.symm.trans known)
        subst mark
        have one : readG05OneRow487 p test i.val ⟨originOrdinal,[],⟨i.val,[]⟩⟩ (signedOrdinal,false) receipt = some row := by
          simpa only [Nat.zero_add] using ran
        obtain ⟨d,source,_,_,obs,_,actualMark⟩ :=
          new_g05_row_preserves_original_slot_signed_bit_observed_keys_and_actual_local_mark487 one
        refine ⟨row,d,atRow,source,
          (the_exact_observation_list_is_empty_without_original_argument_coordinates488
            p gd pos rel (Allowed row.ordinal) i.val row.observed).mpr obs,?_⟩
        cases flag : row.mark with
        | requiredCycle =>
          rw [flag] at actualMark
          have impossible := (a_local_k2_mark_is_exactly_a_checked_true_bit_and_no_local_selection_token487.mp actualMark).1
          cases impossible
        | nonrecursive v =>
          rw [flag] at actualMark
          obtain ⟨_,data,_,decision⟩ :=
            a_local_nonrecursive_mark_requires_a_real_local_receipt_not_failed_read487.mp actualMark
          exact ⟨no_scoped_original_return_when_there_are_no_demanded_coordinates488 p gd pos rel Allowed i.val,
            protocol.1 i.val row.ordinal d data v decision⟩
  · cases run

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
