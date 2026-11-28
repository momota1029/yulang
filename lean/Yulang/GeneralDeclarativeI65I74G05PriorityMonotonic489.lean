import Yulang.GeneralDeclarativeI65I74G05PriorRestriction489

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

theorem independent_g05_actual_cycles_are_monotone_under_inclusion_of_named_prior489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {A B : Nat → CandidateVisitKey485 n → Prop}
    (bigger : ∀ ord key, A ord key → B ord key) (i : Nat)
    (ran : IndependentScopedReturn487 p gd pos rel coords A i) :
    IndependentScopedReturn487 p gd pos rel coords B i := by
  obtain ⟨ord,d,old,root,arg,atArg,head,key,⟨v,trail,proper,needed,which⟩,ending⟩ := ran
  refine ⟨ord,d,old,root,arg,atArg,head,key,⟨v,trail,proper,?_,which⟩,ending⟩
  obtain ⟨same,haveAll⟩ := (independent_g05_prefix_permission_iff_length_and_exact_keys489
    (A ord) _ _ _).mp needed
  exact (independent_g05_prefix_permission_iff_length_and_exact_keys489 (B ord) _ _ _).mpr
    ⟨same,fun k present => bigger _ k (haveAll k present)⟩

private theorem positive_ordinals_behave_monotonically_for_aligned_signs489
    {a b : List (Nat × Bool)} (len : a.length = b.length)
    (each : ∀ (j : Nat) (x y : Nat × Bool), a[j]? = some x → b[j]? = some y →
      x.1 = y.1 ∧ (x.2 = true → y.2 = true)) :
    List.Sublist (positiveOrdinals485 a) (positiveOrdinals485 b) := by
  induction a generalizing b with
  | nil => simp [positiveOrdinals485]
  | cons a tail ih =>
    cases b with
    | nil => simp at len
    | cons b rest =>
      have head := each 0 a b rfl rfl
      have tails := ih (Nat.succ.inj len) (fun j x y one two => each (j+1) x y one two)
      obtain ⟨aOrd,aFlag⟩ := a
      obtain ⟨bOrd,bFlag⟩ := b
      change aOrd = bOrd ∧ (aFlag = true → bFlag = true) at head
      obtain ⟨rfl,monotone⟩ := head
      change List.Sublist (positiveOrdinals485 ((aOrd,aFlag)::tail))
        (positiveOrdinals485 ((aOrd,bFlag)::rest))
      unfold positiveOrdinals485 at tails ⊢
      cases aFlag <;> cases bFlag
      · simpa using tails
      · simpa using List.Sublist.cons aOrd tails
      · cases monotone rfl
      · simpa using List.Sublist.cons_cons aOrd tails

theorem exact_signed_roster_preserves_the_relative_order_of_all_positives_when_their_rule_grows489
    {p : FullProblem} {before after : Nat → Prop} {a b : List (Nat × Bool)}
    (aExact : G05ExactSignedRoster489 p before a) (bExact : G05ExactSignedRoster489 p after b)
    (grows : ∀ i, before i → after i) :
    List.Sublist (positiveOrdinals485 a) (positiveOrdinals485 b) := by
  apply positive_ordinals_behave_monotonically_for_aligned_signs489 (aExact.1.trans bExact.1.symm)
  intro j x y atA atB
  let i : Fin (visible485 p).length := ⟨j, aExact.1 ▸ (List.getElem?_eq_some_iff.mp atA).1⟩
  obtain ⟨aOrd,d,aFlag,origA,knownA,aRule⟩ := aExact.2 i
  obtain ⟨bOrd,e,bFlag,origB,knownB,bRule⟩ := bExact.2 i
  have sameOrd : aOrd = bOrd := congrArg Prod.fst (Option.some.inj
    (((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr origA).symm.trans
       ((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr origB)))
  obtain rfl : x = (aOrd,aFlag) := Option.some.inj (atA.symm.trans knownA)
  obtain rfl : y = (bOrd,bFlag) := Option.some.inj (atB.symm.trans knownB)
  exact ⟨sameOrd,fun yes => bRule.mpr (grows i.val (aRule.mp yes))⟩

theorem any_previously_confirmed_k2s_survive_a_larger_exact_prior_in_the_same_original_order489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {pa pb : Nat → CandidateVisitKey485 n → Bool} {hits : List Nat} {other : PreElection485}
    {A B : Nat → CandidateVisitKey485 n → Prop}
    (before : readG05Preflight489 p gd pos rel coords pa = some (.recursive hits))
    (after : readG05Preflight489 p gd pos rel coords pb = some other)
    (lawA : ∀ ord key, pa ord key = true ↔ A ord key)
    (lawB : ∀ ord key, pb ord key = true ↔ B ord key)
    (bigger : ∀ ord key, A ord key → B ord key) :
    ∃ later, other = .recursive later ∧ List.Sublist hits later := by
  obtain ⟨_,a,aExact,aGate⟩ := g05_preflight_has_the_actual_roots_and_independent_ordered_signs489 before A lawA
  obtain ⟨_,b,bExact,bGate⟩ := g05_preflight_has_the_actual_roots_and_independent_ordered_signs489 after B lawB
  obtain ⟨aHits,nonempty⟩ := signed_gate_recursive_iff_it_returns_the_nonempty_exact_positive_subsequence489.mp aGate
  have inclusion := exact_signed_roster_preserves_the_relative_order_of_all_positives_when_their_rule_grows489
    aExact bExact (independent_g05_actual_cycles_are_monotone_under_inclusion_of_named_prior489 bigger)
  rw [←aHits] at inclusion
  have large : positiveOrdinals485 b ≠ [] := by
    intro no
    rw [no] at inclusion
    exact nonempty (List.sublist_nil.mp inclusion)
  refine ⟨positiveOrdinals485 b,?_ ,inclusion⟩
  exact bGate.symm.trans (signed_gate_recursive_iff_it_returns_the_nonempty_exact_positive_subsequence489.mpr
    ⟨rfl,large⟩)

theorem two_exact_nonempty_g05_scans_are_the_same_even_if_priors_differ_off_actual_trails489
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (pa pb : Nat → CandidateVisitKey485 n → Bool)
    (A B : Nat → CandidateVisitKey485 n → Prop)
    (aScope : G05ExactVisitInputs487 p gd pos rel coords pa A)
    (bScope : G05ExactVisitInputs487 p gd pos rel coords pb B)
    (nonempty : coords ≠ []) (same : G05PriorsAgreeOnOriginalTrails489 p gd pos rel coords A B) :
    ∃ out, readG05Preflight489 p gd pos rel coords pa = some out ∧
      readG05Preflight489 p gd pos rel coords pb = some out := by
  obtain ⟨a,readA⟩ := original_nonempty_g05_demand_replays_full_preflight_without_any_local_receipts489
    p gd pos rel coords pa A aScope nonempty
  obtain ⟨b,readB⟩ := original_nonempty_g05_demand_replays_full_preflight_without_any_local_receipts489
    p gd pos rel coords pb B bScope nonempty
  have eq := two_successful_g05_preflights_agree_when_prior_differs_only_off_actual_original_trails489
    readA readB aScope.1 bScope.1 same
  exact ⟨a,readA,eq.symm ▸ readB⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
