import Yulang.GeneralDeclarativeI65I74PlannedReturnMeaning485

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open GeneralDeclarations (Declaration)

/-- The independent candidate classifier supplies coverage of the actual
original local visits. This is not computed by choosing a winner, and
the data tape alone does not establish it. -/
def IndependentCoverage485 {n : Nat} (p : FullProblem) (pos : Positions n)
    (plans : List (List (CandidateVisitKey485 n))) (ActualRecurs : Nat → Prop) : Prop :=
  ∀ i : Fin (visible485 p).length, ∀ keys, plans[i.val]? = some keys →
    (ActualRecurs i ↔ RecurringPlannedVisit485 p.old.state.core pos keys)

private theorem planned_tape_reads_canonical_index_for_every_visible_candidate
    {Wire : Type} (p : FullProblem) (meaning : CandidateLocal Wire)
    {wires out} (tape : ExactTape485 p meaning (List.range (visible485 p).length) wires out)
    (i : Fin (visible485 p).length) :
    ∃ (ord : Nat) (d : Declaration) (w : Wire) (bit : Bool),
      OriginalRosterCell485 p i.val (ord,d) ∧ wires[i.val]? = some (ord,w) ∧
      meaning ord d w bit ∧ out[i.val]? = some (ord,bit) := by
  obtain ⟨length,_,each⟩ := whole_tape_has_exact_visible_length_and_original_slot_order485 _ _ tape
  have wireLen : wires.length = (visible485 p).length := length.trans List.length_range
  have within : i.val < wires.length := wireLen.symm ▸ i.isLt
  have old : (List.range (visible485 p).length)[i.val]? = some i.val := by
    simp [i.isLt]
  rcases got : wires[i.val]? with _|⟨ord,w⟩
  · rw [List.getElem?_eq_getElem within] at got
    cases got
  · have zipped :
        ((List.range (visible485 p).length).zip wires)[i.val]? = some (i.val,(ord,w)) := by
      exact List.getElem?_zip_eq_some.mpr ⟨old,got⟩
    obtain ⟨row,bit,read,localRun,bitAt⟩ := each i.val _ zipped
    exact ⟨ord,row,w,bit,read,rfl,localRun,bitAt⟩

theorem verified_whole_planned_tape_marks_exactly_the_independently_covered_recursions485
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {plans : List (List (CandidateVisitKey485 n))}
    {permit : Nat → CandidateVisitKey485 n → Bool} {packets : List (Nat × PlannedCandidateWire485 n)}
    {result : PreElection485} (Authorized : Nat → CandidateVisitKey485 n → Prop)
    (permitSound : ∀ i key, permit i key = true → Authorized i key)
    (ActualRecurs : Nat → Prop) (covered : IndependentCoverage485 p pos plans ActualRecurs)
    (ran : readPlannedPreElection485 p gd pos rel plans permit packets = some result) :
    ∃ bits, gate485 bits = result ∧
      ∀ i : Fin (visible485 p).length, ∃ (ord : Nat) (d : Declaration) (bit : Bool),
        OriginalRosterCell485 p i.val (ord,d) ∧ bits[i.val]? = some (ord,bit) ∧
        (bit = true ↔ ActualRecurs i) := by
  unfold readPlannedPreElection485 at ran
  split at ran
  · let reader := readPlannedLocal485 p gd pos rel plans permit
    let actual : CandidateLocal (PlannedCandidateWire485 n) := fun ord d w bit => reader ord d w = some bit
    obtain ⟨bits,tape,final⟩ :=
      (ordered_pre_election_gate_is_exact_on_the_whole_independent_tape485
        p reader actual (fun _ _ _ _ => Iff.rfl) packets result).mp ran
    refine ⟨bits,final,fun i => ?_⟩
    obtain ⟨ord,d,packet,bit,seat,_,localRun,got⟩ :=
      planned_tape_reads_canonical_index_for_every_visible_candidate p actual tape i
    obtain ⟨claimed,keys,signs,filled,exact,signed⟩ :=
      finite_local_tape_result_preserves_the_original_authorized_signed_footprint485
        Authorized permitSound localRun
    have unique := two_visible_slots_cannot_claim_one_original_registry_ordinal485 p claimed seat
    refine ⟨ord,d,bit,seat,got,?_⟩
    rw [←signed]
    exact (signed_footprint_accepts_positive_exactly_for_a_recursive_planned_visit485 exact).trans
      (covered i keys (unique ▸ filled)).symm
  · cases ran

theorem genuine_recursive_visible_candidate_preempts_election_in_every_complete_covered_tape485
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {plans : List (List (CandidateVisitKey485 n))}
    {permit : Nat → CandidateVisitKey485 n → Bool} {packets : List (Nat × PlannedCandidateWire485 n)}
    {result : PreElection485} (Authorized : Nat → CandidateVisitKey485 n → Prop)
    (permitSound : ∀ i key, permit i key = true → Authorized i key)
    (ActualRecurs : Nat → Prop) (covered : IndependentCoverage485 p pos plans ActualRecurs)
    (ran : readPlannedPreElection485 p gd pos rel plans permit packets = some result)
    (i : Fin (visible485 p).length) (recursive : ActualRecurs i) :
    ∃ hits ord d, result = .recursive hits ∧ ord ∈ hits ∧ OriginalRosterCell485 p i.val (ord,d) := by
  obtain ⟨bits,final,exact⟩ :=
    verified_whole_planned_tape_marks_exactly_the_independently_covered_recursions485
      Authorized permitSound ActualRecurs covered ran
  obtain ⟨ord,d,b,old,bitAt,positive⟩ := exact i
  have hit : (ord,true) ∈ bits := by
    have yes := positive.mpr recursive
    subst b
    exact List.mem_of_getElem? bitAt
  obtain ⟨turned,kept⟩ := every_real_positive_is_kept_before_any_election485 bits ord hit
  exact ⟨_,ord,d,final.symm.trans turned,kept,old⟩

theorem no_actual_candidate_recurs_after_a_complete_covered_all_safe_result485
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {plans : List (List (CandidateVisitKey485 n))}
    {permit : Nat → CandidateVisitKey485 n → Bool} {packets : List (Nat × PlannedCandidateWire485 n)}
    {ords : List Nat} (Authorized : Nat → CandidateVisitKey485 n → Prop)
    (permitSound : ∀ i key, permit i key = true → Authorized i key)
    (ActualRecurs : Nat → Prop) (covered : IndependentCoverage485 p pos plans ActualRecurs)
    (ran : readPlannedPreElection485 p gd pos rel plans permit packets = some (.allSafe ords)) :
    ∀ i : Fin (visible485 p).length, ¬ ActualRecurs i := by
  intro i yes
  obtain ⟨hits,ord,d,impossible,_,_⟩ :=
    genuine_recursive_visible_candidate_preempts_election_in_every_complete_covered_tape485
      Authorized permitSound ActualRecurs covered ran i yes
  cases impossible

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
