import Yulang.GeneralDeclarativeI65I74G05ReencodeRows488

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint)
open TypedRootSafety482 (requestRootCheck)

def reencodeG05Report488 {n : Nat} (r : G05Report487 n)
    (computed : List (ComputedOriginalCandidate486 n)) : G05Report487 n :=
  { r with rows := reencodeG05Rows488 r.rows computed }

theorem different_observation_serializations_can_be_transport_to_generated_candidate_scope488
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {coords : List (Fin n)} {permit : Nat → CandidateVisitKey485 n → Bool}
    {palette : SignedPalette486 n} {computed : List (ComputedOriginalCandidate486 n)}
    (made : compileScopedRoster487 p gd pos rel palette coords permit = some computed)
    (length : computed.length = (visible485 p).length)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key)
    (meaning : G05LocalMeaning487) (r : G05Report487 n)
    (exact : G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r) :
    let normalized := reencodeG05Report488 r computed
    g05ReportRowsEquivalent488 normalized.rows r.rows = true ∧
      G05ExactCandidateReport487 p gd pos rel coords Allowed meaning normalized ∧
      ∀ (i : Nat) (a : G05CandidateRow487 n) (c : ComputedOriginalCandidate486 n),
        normalized.rows[i]? = some a → computed[i]? = some c → a.observed = c.keys := by
  let normalized := reencodeG05Report488 r computed
  have count : r.rows.length = computed.length := exact.2.1.trans length.symm
  obtain ⟨len,which⟩ := reencoding_the_report_with_canonical_path_lists_keeps_each_exact_row_identity488 count
  have samePriority : G05PriorityOfRows487 normalized.rows = G05PriorityOfRows487 r.rows :=
    same_ordered_marks_imply_same_prioritized_g05_scope488 (reencoded_g05_rows_keep_the_exact_ordered_marks488 count)
  have normalizedPriority : normalized.priority = G05PriorityOfRows487 normalized.rows :=
    exact.1.trans samePriority.symm
  have same (j : Nat) (before : G05CandidateRow487 n) (atOld : r.rows[j]? = some before) :
      ∃ c : ComputedOriginalCandidate486 n, computed[j]? = some c ∧
        normalized.rows[j]? = some {before with observed := c.keys} ∧
        ∀ key, key ∈ before.observed ↔ key ∈ c.keys := by
    have inside : j < r.rows.length := (List.getElem?_eq_some_iff.mp atOld).1
    let i : Fin (visible485 p).length := ⟨j,exact.2.1 ▸ inside⟩
    obtain ⟨c,e,cAt,roster,_,each⟩ :=
      successful_scoped_roster_reads_every_actual_visible_slot_and_its_exact_independent_visits487
        made i Allowed lawful
    obtain ⟨row,d,seen,origin,keys,_⟩ := exact.2.2 i
    have sameRow : row = before := Option.some.inj (seen.symm.trans atOld)
    subst row
    have ord : before.ordinal = c.authoredOrdinal := congrArg Prod.fst (Option.some.inj
      (((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr origin).symm.trans
        ((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr roster)))
    refine ⟨c,cAt,which j before c atOld cAt,?_⟩
    intro key
    have first := keys key
    rw [ord] at first
    apply first.trans
    apply Iff.trans _ (each key).symm
    constructor
    · rintro ⟨argument,root,old,head,path⟩
      exact ⟨root,argument,old,head,path⟩
    · rintro ⟨root,argument,old,head,path⟩
      exact ⟨argument,root,old,head,path⟩
  have forward : g05ReportRowsEquivalent488 r.rows normalized.rows = true := by
    apply indexed_ordinal_mark_and_visit_membership_reify_report_equivalence488 len.symm
    intro i before after one two
    obtain ⟨c,_,sameRow,keys⟩ := same i before one
    have eq := Option.some.inj (two.symm.trans sameRow)
    subst after
    exact ⟨rfl,rfl,keys⟩
  have reverse : g05ReportRowsEquivalent488 normalized.rows r.rows = true := by
    apply indexed_ordinal_mark_and_visit_membership_reify_report_equivalence488 len
    intro i after before two one
    obtain ⟨c,_,sameRow,keys⟩ := same i before one
    have eq := Option.some.inj (two.symm.trans sameRow)
    subst after
    exact ⟨rfl,rfl,fun key => (keys key).symm⟩
  refine ⟨reverse,g05_serialization_equivalence_preserves_the_independent_full_report488
    forward normalizedPriority exact,?_⟩
  intro j row calculated atNew atComp
  have index : j < normalized.rows.length := (List.getElem?_eq_some_iff.mp atNew).1
  have inside : j < r.rows.length := len ▸ index
  let old := r.rows[j]
  have oldExists : r.rows[j]? = some old := List.getElem?_eq_getElem inside
  obtain ⟨c,cAt,normalizedAt,_⟩ := same j old oldExists
  have cmp : c = calculated := Option.some.inj (cAt.symm.trans atComp)
  have fresh : row = {old with observed := c.keys} := Option.some.inj (atNew.symm.trans normalizedAt)
  rw [fresh,cmp]

private theorem successful_optimizer_does_not_change_source_list_length488
    {α β : Type} {a : List α} {b : List β} {f : α → Option β}
    (encoded : a.mapM (m := Option) f = some b) : b.length = a.length := by
  induction a generalizing b with
  | nil =>
    have h : [] = b := Option.some.inj encoded
    subst b
    rfl
  | cons x tail ih =>
    cases fn : f x with
    | none => simp [List.mapM_cons,fn] at encoded
    | some head =>
      cases later : tail.mapM (m := Option) f with
      | none => simp [List.mapM_cons,fn,later] at encoded
      | some back =>
        have exact : head::back = b := Option.some.inj (by simpa [List.mapM_cons,fn,later] using encoded)
        subst b
        exact congrArg Nat.succ (ih later)

theorem each_independently_exact_noncanonical_g05_report_has_a_finite_equivalence_witness_under_actual_arity488
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (check : G05LocalChecker487)
    (Allowed : Nat → CandidateVisitKey485 n → Prop) (meaning : G05LocalMeaning487)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (protocol : G05ExactLocalProtocol487 check meaning)
    (arity : ∀ (i : Nat) (d : GeneralDeclarations.Declaration), (visible485 p)[i]? = some d →
      d.head.length = p.old.root.demand.arguments.length)
    (r : G05Report487 n)
    (exact : G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r) :
    ∃ wire : G05FiniteWitness487 n, wire.roots.map Checkpoint.which = coords ∧
      checkFlatWithEquivalentG05Tag488 p gd pos rel coords permit check (.inr r) (.inr wire) = true := by
  have saved := scope
  obtain ⟨lawful,coherence,root,guard,starts⟩ := scope
  obtain ⟨nodes,rootMade,points⟩ :=
    given_exact_old_guarded_safe_roots_the_computer_returns_all_in_same_order487 root guard
  have checked : requestRootCheck p pos rel nodes = true :=
    computed_original_roots_pass_unmodified_ordered_request_root_check487 _ _ _ _ _ rootMade
  have count : nodes.length = p.old.root.demand.arguments.length := by
    simpa only [List.length_map] using (all_checked_request_roots_carry_guards_and_exact_list_length487 checked).1
  let palette := computedOriginalPalette486 p.old.state.core pos rel
  have complete : CompletePalette486 p.old.state.core pos rel palette :=
    real_existing_graph_finitely_computes_its_verified_optional_palette486 _ _ _
  obtain ⟨produced,signs,compiled,_,_⟩ :=
    independently_scoped_all_canonical_head_coordinates_produce_a_rechecked_whole_tape486
      p gd pos rel palette complete nodes permit Allowed (fun ord key => (lawful ord key).mp)
      checked count arity (fun i arg site h => starts i arg site (by simpa only [points] using h))
  have scopedGen : compileScopedRoster487 p gd pos rel palette coords permit = some produced := by
    rw [scoped_roster_reproduces_the_exact_old_packets_in_original_visible_order487
      (gd := gd) complete coords permit guard coherence]
    simpa only [points] using compiled
  have length : produced.length = (visible485 p).length := by
    simpa only [List.length_range] using successful_optimizer_does_not_change_source_list_length488 scopedGen
  let normalized := reencodeG05Report488 r produced
  obtain ⟨equivalent,independent,canonicalOrder⟩ :=
    different_observation_serializations_can_be_transport_to_generated_candidate_scope488
      scopedGen length Allowed lawful meaning r exact
  obtain ⟨wire,drawn,verified⟩ := g05_canonical_exact_report_reifies_under_the_named_visit_and_local_protocols487
    p gd pos rel coords permit check Allowed meaning saved protocol arity normalized independent
    (fun second ran => by
      have same : produced = second := Option.some.inj (scopedGen.symm.trans ran)
      subst second
      exact canonicalOrder)
  have read := new_tag_check_succeeds_iff_it_replays_the_same_full_report_data487.mp verified
  refine ⟨wire,drawn,?_⟩
  change checkFlatWithEquivalentG05Tag488 p gd pos rel coords permit check (.inr r) (.inr wire) = true
  simp only [checkFlatWithEquivalentG05Tag488,read]
  exact Bool.and_eq_true_iff.mpr ⟨equivalent,decide_eq_true exact.1⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
