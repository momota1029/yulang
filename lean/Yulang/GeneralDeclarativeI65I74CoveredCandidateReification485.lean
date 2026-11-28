import Yulang.GeneralDeclarativeI65I74CoveredCandidatePriority485

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open GeneralDeclarations (Declaration)

theorem independently_typed_planned_local_routes_have_same_guarded_tape_packet485
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {plans : List (List (CandidateVisitKey485 n))}
    {permit : Nat → CandidateVisitKey485 n → Bool} {Auth : Nat → CandidateVisitKey485 n → Prop}
    (recognizes : ∀ i key, Auth i key → permit i key = true) {i ord : Nat} {d : Declaration}
    {keys wires bits} (slot : OriginalRosterCell485 p i (ord,d))
    (schedule : plans[i]? = some keys)
    (independent : ExactCandidateFootprint485 p gd pos rel i (Auth i) keys wires bits) :
    ∃ packet : PlannedCandidateWire485 n, packet.visibleOrdinal = i ∧
      packet.paths.map candidateVisitKey485 = keys ∧
      readPlannedLocal485 p gd pos rel plans permit ord d packet = some (bits.any id) := by
  obtain ⟨ws,same,completed⟩ := every_independently_permitted_plan_reifies_same_keys_and_signed_results485
    (permit i) (recognizes i) independent
  have original := (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr slot
  refine ⟨⟨i,ws⟩,rfl,same,?_⟩
  simp [readPlannedLocal485,original,schedule,completed,Option.bind]

private theorem every_independently_traced_roster_reifies_a_whole_ordered_tape
    {Wire : Type} (p : FullProblem) (check : CandidateCheck Wire) (slots : List Nat)
    (each : ∀ i ∈ slots, ∃ ord d w bit,
      OriginalRosterCell485 p i (ord,d) ∧ check ord d w = some bit) :
    ∃ packets bits, replaySlots485 p check slots packets = some bits := by
  induction slots with
  | nil => exact ⟨[],[],rfl⟩
  | cons i other ih =>
    obtain ⟨ord,d,w,sign,slot,read⟩ := each i (List.mem_cons_self ..)
    obtain ⟨packets,bits,later⟩ :=
      ih (fun j here => each j (List.mem_cons_of_mem _ here))
    have original := (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr slot
    exact ⟨(ord,w)::packets,(ord,sign)::bits,by simp [replaySlots485,original,read,later,Option.bind]⟩

/-- Complete relative to independently given authority and the finite
planned visits on every unaltered visible row. This does not construct
those source classifications or extend the installed top entry. -/
theorem all_independently_planned_visible_candidates_have_one_finite_priority_tape485
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {plans : List (List (CandidateVisitKey485 n))}
    {permit : Nat → CandidateVisitKey485 n → Bool} {Auth : Nat → CandidateVisitKey485 n → Prop}
    (recognizes : ∀ i key, Auth i key → permit i key = true)
    (allSchedules : plans.length = (visible485 p).length)
    (available : ∀ i : Fin (visible485 p).length, ∃ keys wires bits,
      plans[i.val]? = some keys ∧ ExactCandidateFootprint485 p gd pos rel i.val (Auth i) keys wires bits) :
    ∃ packets bits,
      readTape485 p (readPlannedLocal485 p gd pos rel plans permit) packets = some bits ∧
      readPlannedPreElection485 p gd pos rel plans permit packets = some (gate485 bits) := by
  obtain ⟨packets,bits,ran⟩ :=
    every_independently_traced_roster_reifies_a_whole_ordered_tape
      p (readPlannedLocal485 p gd pos rel plans permit) (List.range (visible485 p).length)
      (fun index included => by
        have valid : index < (visible485 p).length := List.mem_range.mp included
        let i : Fin (visible485 p).length := ⟨index,valid⟩
        obtain ⟨keys,old,bits,scheduled,proof⟩ := available i
        obtain ⟨⟨ord,d⟩,source⟩ := no_visible_slot_is_lost_in_the_exact_roster485 p i
        have seat := (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mp source
        obtain ⟨packet,_,_,verified⟩ :=
          independently_typed_planned_local_routes_have_same_guarded_tape_packet485
            recognizes seat scheduled proof
        exact ⟨ord,d,packet,_,seat,verified⟩)
  exact ⟨packets,bits,ran,by simp [readPlannedPreElection485,allSchedules,beforeElection485,readTape485,ran]⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
