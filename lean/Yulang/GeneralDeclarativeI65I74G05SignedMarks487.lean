import Yulang.GeneralDeclarativeI65I74G05OrderedMarks487
import Yulang.GeneralDeclarativeI65I74G05TaggedEntry487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open GeneralDeclarations (Declaration)

theorem stored_g05_signed_bits_cover_the_same_independent_recursive_candidates487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {coords : List (Fin n)} {permit : Nat → CandidateVisitKey485 n → Bool}
    {computed : List (ComputedOriginalCandidate486 n)} {tape : List (Nat × PlannedCandidateWire485 n)}
    {bits : List (Nat × Bool)}
    (computedAt : compileScopedRoster487 p gd pos rel palette coords permit = some computed)
    (ran : readTape485 p
      (readPlannedLocal485 p gd pos rel (computed.map ComputedOriginalCandidate486.keys)
        (permitAtOriginalVisibleSlot486 p permit)) tape = some bits)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key) :
    bits.length = (visible485 p).length ∧
    ∀ i : Fin (visible485 p).length, ∃ ord d bit,
      OriginalRosterCell485 p i.val (ord,d) ∧ bits[i.val]? = some (ord,bit) ∧
      (bit = true ↔ IndependentScopedReturn487 p gd pos rel coords Allowed i) := by
  let required := computed.map ComputedOriginalCandidate486.keys
  let slotPermit := permitAtOriginalVisibleSlot486 p permit
  let reader := readPlannedLocal485 p gd pos rel required slotPermit
  let interpretBit : CandidateLocal (PlannedCandidateWire485 n) :=
    fun ord d w b => reader ord d w = some b
  have signed := (read_tape_reflects_the_actual_entire_visible_order485
    p reader interpretBit (fun _ _ _ _ => Iff.rfl) tape bits).mp ran
  obtain ⟨count,all,facts⟩ := whole_tape_has_exact_visible_length_and_original_slot_order485 p interpretBit signed
  have exactCoverage := compiled_scoped_tape_covers_its_independent_original_recursion_predicate487
    computedAt Allowed lawful
  have authority := permit_at_original_slot_only_uses_authority_from_its_actual_original_ordinal487 (p := p)
    (fun ord key => (lawful ord key).mp)
  refine ⟨by simpa only [List.length_range] using all,?_⟩
  intro i
  have onList : i.val < tape.length := by simpa only [count,List.length_range] using i.isLt
  let item := tape[i.val]
  have indexed : tape[i.val]? = some item := List.getElem?_eq_getElem onList
  have linked : ((List.range (visible485 p).length).zip tape)[i.val]? = some (i.val,item) :=
    List.getElem?_zip_eq_some.mpr ⟨List.getElem?_range i.isLt,indexed⟩
  obtain ⟨d,bit,original,localRun,atIndex⟩ := facts i.val _ linked
  have close : reader item.1 d item.2 = some bit := localRun
  obtain ⟨used,keys,values,atKeys,valid,signedResult⟩ :=
    finite_local_tape_result_preserves_the_original_authorized_signed_footprint485
      (IndependentlyAuthorizedAtVisibleSlot487 p Allowed) authority close
  have same : item.2.visibleOrdinal = i.val :=
    two_visible_slots_cannot_claim_one_original_registry_ordinal485 p used original
  rw [same] at atKeys
  refine ⟨item.1,d,bit,original,atIndex,?_⟩
  rw [←signedResult]
  exact (signed_footprint_accepts_positive_exactly_for_a_recursive_planned_visit485 valid).trans
    (exactCoverage i keys atKeys).symm

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
