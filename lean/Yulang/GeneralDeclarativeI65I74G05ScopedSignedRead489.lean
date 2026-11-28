import Yulang.GeneralDeclarativeI65I74G05ExactSignedRoster489

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint)
open TypedRootSafety482 (AllRootSafe)

/-- Retains length as well as each independently classified slot. -/
theorem verified_planned_g05_gate_has_exact_complete_signed_roster489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {plans : List (List (CandidateVisitKey485 n))}
    {permit : Nat → CandidateVisitKey485 n → Bool} {packets : List (Nat × PlannedCandidateWire485 n)}
    {result : PreElection485} (Authorized : Nat → CandidateVisitKey485 n → Prop)
    (permitSound : ∀ i key, permit i key = true → Authorized i key)
    (ActualRecurs : Nat → Prop) (covered : IndependentCoverage485 p pos plans ActualRecurs)
    (ran : readPlannedPreElection485 p gd pos rel plans permit packets = some result) :
    ∃ bits, G05ExactSignedRoster489 p ActualRecurs bits ∧ gate485 bits = result := by
  unfold readPlannedPreElection485 at ran
  split at ran
  · let reader := readPlannedLocal485 p gd pos rel plans permit
    let meaning : CandidateLocal (PlannedCandidateWire485 n) := fun ord d wire flag =>
      reader ord d wire = some flag
    obtain ⟨bits,tape,gate⟩ :=
      (ordered_pre_election_gate_is_exact_on_the_whole_independent_tape485
        p reader meaning (fun _ _ _ _ => Iff.rfl) packets result).mp ran
    obtain ⟨packetLen,bitsLen,indexed⟩ :=
      whole_tape_has_exact_visible_length_and_original_slot_order485 p meaning tape
    refine ⟨bits,⟨bitsLen.trans List.length_range,?_⟩,gate⟩
    intro i
    have within : i.val < packets.length := by simpa only [packetLen,List.length_range] using i.isLt
    let slot := packets[i.val]'within
    have packetAt : packets[i.val]? = some slot := List.getElem?_eq_getElem within
    have atRange : (List.range (visible485 p).length)[i.val]? = some i.val := by simp [i.isLt]
    have zipped :
        ((List.range (visible485 p).length).zip packets)[i.val]? = some (i.val,slot) :=
      List.getElem?_zip_eq_some.mpr ⟨atRange,packetAt⟩
    obtain ⟨d,flag,origin,localRun,bitAt⟩ := indexed i.val _ zipped
    obtain ⟨packetOrigin,keys,signs,keyAt,realFootprint,signed⟩ :=
      finite_local_tape_result_preserves_the_original_authorized_signed_footprint485
        Authorized permitSound localRun
    have original := two_visible_slots_cannot_claim_one_original_registry_ordinal485 p packetOrigin origin
    change slot.2.visibleOrdinal = i.val at original
    have keysAt : plans[i.val]? = some keys := by simpa only [original] using keyAt
    refine ⟨slot.1,d,flag,origin,bitAt,?_⟩
    rw [←signed]
    exact (signed_footprint_accepts_positive_exactly_for_a_recursive_planned_visit485 realFootprint).trans
      (covered i keys keysAt).symm
  · cases ran

theorem successful_scoped_g05_read_returns_exact_original_root_and_signed_roster489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {roots : List (Checkpoint n)} {permit : Nat → CandidateVisitKey485 n → Bool}
    {out : PreElection485}
    (ran : readScopedPreElection487 p gd pos rel palette roots permit = some out)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key) :
    AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (·.lower)) (roots.map Checkpoint.which) ∧
      ∃ bits, G05ExactSignedRoster489 p (IndependentScopedReturn487 p gd pos rel
        (roots.map Checkpoint.which) Allowed) bits ∧ gate485 bits = out := by
  obtain ⟨rootIsActual,rows,compiled,replayed⟩ :=
    scoped_election_checks_unchanged_safe_original_roots_and_full_packet_tape487 ran
  refine ⟨rootIsActual,?_⟩
  apply verified_planned_g05_gate_has_exact_complete_signed_roster489
    (IndependentlyAuthorizedAtVisibleSlot487 p Allowed) _
    (IndependentScopedReturn487 p gd pos rel (roots.map Checkpoint.which) Allowed) _ replayed
  · exact permit_at_original_slot_only_uses_authority_from_its_actual_original_ordinal487
      (fun ord key => (lawful ord key).mp)
  · exact compiled_scoped_tape_covers_its_independent_original_recursion_predicate487 compiled Allowed lawful

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
