import Yulang.GeneralDeclarativeI65I74G05K2BeforeLocal489

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

theorem an_original_ordinal_is_positive_exactly_when_its_visible_slot_really_recurs489
    {p : FullProblem} {recurs : Nat → Prop} {bits : List (Nat × Bool)}
    (exactRoster : G05ExactSignedRoster489 p recurs bits) (ord : Nat) :
    ord ∈ positiveOrdinals485 bits ↔
      ∃ i : Fin (visible485 p).length, (∃ d, OriginalRosterCell485 p i.val (ord,d)) ∧ recurs i.val := by
  rw [positive_ordinal_is_a_real_positive_local_tape_slot485]
  constructor
  · intro has
    obtain ⟨j,inBounds,atJ⟩ := List.mem_iff_getElem.mp has
    let i : Fin (visible485 p).length := ⟨j,exactRoster.1 ▸ inBounds⟩
    have indexed : bits[i.val]? = some (ord,true) := by
      rw [List.getElem?_eq_getElem inBounds,atJ]
    obtain ⟨physical,d,bit,original,recorded,exactMark⟩ := exactRoster.2 i
    have same := Option.some.inj (recorded.symm.trans indexed)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
    exact ⟨i,⟨d,original⟩,exactMark.mp rfl⟩
  · rintro ⟨i,⟨d,old⟩,positive⟩
    obtain ⟨physical,e,bit,original,recorded,exactMark⟩ := exactRoster.2 i
    have same : physical = ord := congrArg Prod.fst (Option.some.inj
      (((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr original).symm.trans
        ((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr old)))
    have yes := exactMark.mpr positive
    rw [same,yes] at recorded
    exact List.mem_of_getElem? recorded

theorem signed_gate_recursive_iff_it_returns_the_nonempty_exact_positive_subsequence489
    {bits : List (Nat × Bool)} {hits : List Nat} :
    gate485 bits = .recursive hits ↔ hits = positiveOrdinals485 bits ∧ hits ≠ [] := by
  unfold gate485
  cases found : positiveOrdinals485 bits with
  | nil => simp
  | cons head rest =>
    constructor
    · intro classified
      have same := (PreElection485.recursive.inj classified).symm
      exact ⟨same,by rw [same]; exact List.cons_ne_nil _ _⟩
    · rintro ⟨rfl,_⟩
      rfl

theorem a_successful_positive_g05_preflight_lists_every_and_only_the_actual_original_k2_slots489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {hits : List Nat}
    (ran : readG05Preflight489 p gd pos rel coords permit = some (.recursive hits))
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key) :
    hits ≠ [] ∧ ∀ ord, ord ∈ hits ↔
      ∃ i : Fin (visible485 p).length, (∃ d, OriginalRosterCell485 p i.val (ord,d)) ∧
        IndependentScopedReturn487 p gd pos rel coords Allowed i.val := by
  obtain ⟨_,bits,ledger,gate⟩ := g05_preflight_has_the_actual_roots_and_independent_ordered_signs489 ran Allowed lawful
  obtain ⟨same,nonempty⟩ := signed_gate_recursive_iff_it_returns_the_nonempty_exact_positive_subsequence489.mp gate
  exact ⟨nonempty,fun ord => same ▸ an_original_ordinal_is_positive_exactly_when_its_visible_slot_really_recurs489 ledger ord⟩

theorem a_real_independent_g05_k2_on_nonempty_original_demand_replays_without_any_local_matcher489
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (nonempty : coords ≠ []) (i : Fin (visible485 p).length)
    (recurs : IndependentScopedReturn487 p gd pos rel coords Allowed i.val) :
    ∃ hits, readG05Preflight489 p gd pos rel coords permit = some (.recursive hits) ∧
      ∃ ord d, OriginalRosterCell485 p i.val (ord,d) ∧ ord ∈ hits := by
  obtain ⟨out,ran⟩ := original_nonempty_g05_demand_replays_full_preflight_without_any_local_receipts489
    p gd pos rel coords permit Allowed scope nonempty
  obtain ⟨_,bits,ledger,gate⟩ := g05_preflight_has_the_actual_roots_and_independent_ordered_signs489 ran Allowed scope.1
  obtain ⟨ord,d,bit,original,observed,iffMeaning⟩ := ledger.2 i
  have yes := iffMeaning.mpr recurs
  rw [yes] at observed
  obtain ⟨classified,member⟩ := every_real_positive_is_kept_before_any_election485 bits ord (List.mem_of_getElem? observed)
  refine ⟨positiveOrdinals485 bits,?_ ,ord,d,original,member⟩
  rw [← classified,gate]
  exact ran

theorem all_safe_g05_preflight_certifies_no_actual_k2_at_any_original_candidate489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {ords : List Nat}
    (ran : readG05Preflight489 p gd pos rel coords permit = some (.allSafe ords))
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key) :
    ∀ i : Fin (visible485 p).length, ¬ IndependentScopedReturn487 p gd pos rel coords Allowed i.val := by
  obtain ⟨_,bits,ledger,gate⟩ := g05_preflight_has_the_actual_roots_and_independent_ordered_signs489 ran Allowed lawful
  have allSafe := (safe_before_election_means_every_exact_slot_has_negative_result485 bits ords).mp gate
  intro i actual
  obtain ⟨ord,d,_,atSource,_,_⟩ := ledger.2 i
  have member := (an_original_ordinal_is_positive_exactly_when_its_visible_slot_really_recurs489 ledger ord).mpr
    ⟨i,⟨d,atSource⟩,actual⟩
  exact allSafe.2 ord ((positive_ordinal_is_a_real_positive_local_tape_slot485 bits ord).mp member)

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
