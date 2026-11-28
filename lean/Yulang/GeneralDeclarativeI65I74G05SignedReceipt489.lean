import Yulang.GeneralDeclarativeI65I74G05ExactPreflightHits489

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint)
open TypedRootSafety482 (requestRootCheck requestRootCheckSound AllRootSafe)

structure G05SignedReceipt489 (n : Nat) where
  roots : List (Checkpoint n)
  authoredTape : List (Nat × PlannedCandidateWire485 n)

/-- Recheck a complete signed transcript at the same accepted old roots.
No candidate marks or local receipts are accepted as input. -/
def readG05SignedReceipt489 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (coords : List (Fin n)) (permit : Nat → CandidateVisitKey485 n → Bool)
    (receipt : G05SignedReceipt489 n) : Option PreElection485 :=
  if decide (receipt.roots.map Checkpoint.which = coords) && requestRootCheck p pos rel receipt.roots then do
    let computed ← compileScopedRoster487 p gd pos rel (computedOriginalPalette486 p.old.state.core pos rel)
      coords permit
    readPlannedPreElection485 p gd pos rel (computed.map ComputedOriginalCandidate486.keys)
      (permitAtOriginalVisibleSlot486 p permit) receipt.authoredTape
  else none

theorem signed_g05_receipt_success_rechecks_the_original_roots_and_whole_candidate_plan489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {receipt : G05SignedReceipt489 n}
    {out : PreElection485}
    (ran : readG05SignedReceipt489 p gd pos rel coords permit receipt = some out) :
    receipt.roots.map Checkpoint.which = coords ∧
    requestRootCheck p pos rel receipt.roots = true ∧
    ∃ computed, compileScopedRoster487 p gd pos rel (computedOriginalPalette486 p.old.state.core pos rel)
      coords permit = some computed ∧
    readPlannedPreElection485 p gd pos rel (computed.map ComputedOriginalCandidate486.keys)
      (permitAtOriginalVisibleSlot486 p permit) receipt.authoredTape = some out := by
  unfold readG05SignedReceipt489 at ran
  split at ran
  · rename_i rootOK
    obtain ⟨coordinate,guard⟩ := Bool.and_eq_true_iff.mp rootOK
    refine ⟨of_decide_eq_true coordinate,guard,?_⟩
    cases h : compileScopedRoster487 p gd pos rel (computedOriginalPalette486 p.old.state.core pos rel)
      coords permit with
    | none => simp [h] at ran
    | some computed => exact ⟨computed,rfl,by simpa [h] using ran⟩
  · cases ran

theorem any_checked_signed_g05_receipt_has_its_full_independent_original_signed_roster489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {receipt : G05SignedReceipt489 n}
    {out : PreElection485}
    (ran : readG05SignedReceipt489 p gd pos rel coords permit receipt = some out)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key) :
    AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (·.lower)) coords ∧
      ∃ bits, G05ExactSignedRoster489 p (IndependentScopedReturn487 p gd pos rel coords Allowed) bits ∧
        gate485 bits = out := by
  obtain ⟨roots,guard,computed,compile,reading⟩ :=
    signed_g05_receipt_success_rechecks_the_original_roots_and_whole_candidate_plan489 ran
  refine ⟨roots ▸ requestRootCheckSound p pos rel receipt.roots guard,?_⟩
  apply verified_planned_g05_gate_has_exact_complete_signed_roster489
    (IndependentlyAuthorizedAtVisibleSlot487 p Allowed) _
    (IndependentScopedReturn487 p gd pos rel coords Allowed) _ reading
  · exact permit_at_original_slot_only_uses_authority_from_its_actual_original_ordinal487
      (fun ord key => (lawful ord key).mp)
  · exact compiled_scoped_tape_covers_its_independent_original_recursion_predicate487 compile Allowed lawful

theorem successfully_read_signed_g05_receipt_keeps_a_packet_for_every_visible_candidate489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {receipt : G05SignedReceipt489 n}
    {out : PreElection485}
    (ran : readG05SignedReceipt489 p gd pos rel coords permit receipt = some out) :
    receipt.authoredTape.length = (visible485 p).length := by
  obtain ⟨_,_,computed,_,reading⟩ :=
    signed_g05_receipt_success_rechecks_the_original_roots_and_whole_candidate_plan489 ran
  unfold readPlannedPreElection485 at reading
  split at reading
  · let parser := readPlannedLocal485 p gd pos rel (computed.map ComputedOriginalCandidate486.keys)
      (permitAtOriginalVisibleSlot486 p permit)
    let meaning : CandidateLocal (PlannedCandidateWire485 n) := fun ord d wire flag =>
      parser ord d wire = some flag
    obtain ⟨bits,actual,_⟩ :=
      (ordered_pre_election_gate_is_exact_on_the_whole_independent_tape485 p parser meaning
        (fun _ _ _ _ => Iff.rfl) receipt.authoredTape out).mp reading
    exact (whole_tape_has_exact_visible_length_and_original_slot_order485 p meaning actual).1.trans List.length_range
  · cases reading

theorem incomplete_signed_g05_transcript_returns_none_never_an_all_safe_result489
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (receipt : G05SignedReceipt489 n)
    (dropped : receipt.authoredTape.length ≠ (visible485 p).length) :
    readG05SignedReceipt489 p gd pos rel coords permit receipt = none := by
  cases read : readG05SignedReceipt489 p gd pos rel coords permit receipt with
  | none => rfl
  | some out =>
    exact False.elim
      (dropped (successfully_read_signed_g05_receipt_keeps_a_packet_for_every_visible_candidate489 read))

theorem every_successful_automatic_g05_preflight_reifies_one_local_token_free_signed_receipt489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {out : PreElection485}
    (ran : readG05Preflight489 p gd pos rel coords permit = some out) :
    ∃ receipt : G05SignedReceipt489 n, receipt.roots.map Checkpoint.which = coords ∧
      readG05SignedReceipt489 p gd pos rel coords permit receipt = some out := by
  unfold readG05Preflight489 at ran
  cases h : computedOriginalRootCertificates487 p.old.state.core pos rel
      (p.old.root.demand.arguments.map (·.lower)) with
  | none => simp [h] at ran
  | some roots =>
    simp only [h,bind,Option.bind] at ran
    split at ran
    · rename_i coordinate
      obtain ⟨_,computed,compile,reading⟩ :=
        scoped_election_checks_unchanged_safe_original_roots_and_full_packet_tape487 ran
      have guarded : requestRootCheck p pos rel roots = true :=
        computed_original_roots_pass_unmodified_ordered_request_root_check487 _ _ _ _ _ h
      let receipt : G05SignedReceipt489 n :=
        ⟨roots,computed.map (fun row => (row.authoredOrdinal,row.packet))⟩
      refine ⟨receipt,coordinate,?_⟩
      have exactCompile := coordinate ▸ compile
      simp [readG05SignedReceipt489,receipt,coordinate,guarded,exactCompile,reading]
    · cases ran

theorem any_successfully_replayed_g05_signed_receipt_matches_an_automatic_scan_on_its_exact_scope489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {receipt : G05SignedReceipt489 n}
    {given auto : PreElection485}
    (received : readG05SignedReceipt489 p gd pos rel coords permit receipt = some given)
    (scanned : readG05Preflight489 p gd pos rel coords permit = some auto)
    (Allowed : Nat → CandidateVisitKey485 n → Prop) (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key) :
    given = auto := by
  obtain ⟨_,a,aLedger,aGate⟩ := any_checked_signed_g05_receipt_has_its_full_independent_original_signed_roster489
    received Allowed lawful
  obtain ⟨_,b,bLedger,bGate⟩ := g05_preflight_has_the_actual_roots_and_independent_ordered_signs489
    scanned Allowed lawful
  rw [exact_g05_signed_roster_is_unique_in_original_order489 aLedger bLedger] at aGate
  exact aGate.symm.trans bGate

theorem nonempty_original_g05_preflight_result_is_iff_existence_of_a_matching_checked_signed_receipt489
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (nonempty : coords ≠ []) (out : PreElection485) :
    readG05Preflight489 p gd pos rel coords permit = some out ↔
      ∃ receipt : G05SignedReceipt489 n, readG05SignedReceipt489 p gd pos rel coords permit receipt = some out := by
  constructor
  · intro ran
    obtain ⟨receipt,_,replayed⟩ := every_successful_automatic_g05_preflight_reifies_one_local_token_free_signed_receipt489 ran
    exact ⟨receipt,replayed⟩
  · rintro ⟨receipt,replayed⟩
    obtain ⟨auto,scanned⟩ := original_nonempty_g05_demand_replays_full_preflight_without_any_local_receipts489
      p gd pos rel coords permit Allowed scope nonempty
    have same := any_successfully_replayed_g05_signed_receipt_matches_an_automatic_scan_on_its_exact_scope489
      replayed scanned Allowed scope.1
    exact scanned.trans (congrArg some same.symm)

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
