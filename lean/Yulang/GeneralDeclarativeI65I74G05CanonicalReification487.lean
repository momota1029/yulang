import Yulang.GeneralDeclarativeI65I74G05LocalTokenReification487
import Yulang.GeneralDeclarativeI65I74AutomaticScopedElection487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint GuardedObservationInput)
open TypedRootSafety482 (requestRootCheck)
open GeneralDeclarations (Declaration)

private theorem some_list_effect_keeps_the_exact_number_of_inputs487
    {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (ran : xs.mapM (m := Option) f = some ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil =>
    have same : [] = ys := Option.some.inj ran
    subst ys
    rfl
  | cons x rest ih =>
    cases front : f x with
    | none => simp [List.mapM_cons,front] at ran
    | some y =>
      cases after : rest.mapM (m := Option) f with
      | none => simp [List.mapM_cons,front,after] at ran
      | some later =>
        have all : y::later = ys := Option.some.inj (by simpa [List.mapM_cons,front,after] using ran)
        subst ys
        exact congrArg Nat.succ (ih after)

private theorem same_roster_slot_fixes_original_id_and_declaration487
    {p : FullProblem} {i a b : Nat} {d e : Declaration}
    (first : OriginalRosterCell485 p i (a,d)) (second : OriginalRosterCell485 p i (b,e)) :
    (a,d) = (b,e) := Option.some.inj
  (((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr first).symm.trans
    ((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr second))

theorem a_signed_tape_and_exact_canonical_local_reports_supply_finite_checked_tokens487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {coords : List (Fin n)} {permit : Nat → CandidateVisitKey485 n → Bool}
    {check : G05LocalChecker487} {meaning : G05LocalMeaning487}
    {computed : List (ComputedOriginalCandidate486 n)} {tape : List (Nat × PlannedCandidateWire485 n)}
    {signs : List (Nat × Bool)} {r : G05Report487 n}
    (compiled : compileScopedRoster487 p gd pos rel palette coords permit = some computed)
    (signed : readTape485 p
      (readPlannedLocal485 p gd pos rel (computed.map ComputedOriginalCandidate486.keys)
        (permitAtOriginalVisibleSlot486 p permit)) tape = some signs)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key)
    (report : G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r)
    (canonicalOrder : ∀ (i : Nat) (a : G05CandidateRow487 n) (c : ComputedOriginalCandidate486 n),
      r.rows[i]? = some a → computed[i]? = some c → a.observed = c.keys)
    (localComplete : ∀ i ord d v, meaning i ord d v → ∃ data, check i ord d data = some v) :
    ∃ tokens, readG05OrderedRows487 p check 0 computed signs tokens = some r.rows := by
  have cLength : computed.length = (visible485 p).length := by
    simpa only [List.length_range] using some_list_effect_keeps_the_exact_number_of_inputs487 compiled
  have enough : computed.length = r.rows.length := cLength.trans report.2.1.symm
  obtain ⟨sLength,scope⟩ :=
    stored_g05_signed_bits_cover_the_same_independent_recursive_candidates487 compiled signed Allowed lawful
  apply exact_locally_available_marks_reify_one_finite_ordered_local_receipt_list487
    p check 0 computed signs r.rows enough (sLength.trans report.2.1.symm)
  intro j target sign row atTarget atBit atRow
  have inside : j < r.rows.length := (List.getElem?_eq_some_iff.mp atRow).1
  let i : Fin (visible485 p).length := ⟨j,report.2.1 ▸ inside⟩
  obtain ⟨actual,d,exactRow,source,_,explained⟩ := report.2.2 i
  have hrow : actual = row := Option.some.inj (exactRow.symm.trans atRow)
  subst actual
  obtain ⟨other,e,bit,signedCell,placed,meaningBit⟩ := scope i
  have copied : sign = (other,bit) := Option.some.inj (atBit.symm.trans placed)
  subst sign
  have ord : row.ordinal = other := congrArg Prod.fst
    (same_roster_slot_fixes_original_id_and_declaration487 source signedCell)
  obtain ⟨which,actualD,computedAt,actualCell,slot,_⟩ :=
    successful_scoped_roster_reads_every_actual_visible_slot_and_its_exact_independent_visits487
      compiled i Allowed lawful
  have same : target = which := Option.some.inj (atTarget.symm.trans computedAt)
  subst which
  have visible : j = target.packet.visibleOrdinal := slot.symm
  have finalOrd : row.ordinal = target.authoredOrdinal := congrArg Prod.fst
    (same_roster_slot_fixes_original_id_and_declaration487 source actualCell)
  have sourceRead : rosterCell485 p j = some (row.ordinal,d) :=
    (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr source
  have ordered : (decide (row.ordinal = other) && decide (row.ordinal = target.authoredOrdinal) &&
      decide (j = target.packet.visibleOrdinal)) = true :=
    Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true ord,decide_eq_true finalOrd⟩,decide_eq_true visible⟩
  have keys := canonicalOrder j row target atRow atTarget
  cases mark : row.mark with
  | requiredCycle =>
    rw [mark] at explained
    have value : bit = true := meaningBit.mpr explained
    refine ⟨none,?_⟩
    rw [Nat.zero_add,readG05OneRow487]
    simp only [sourceRead,bind,Option.bind]
    rw [ite_eq_left ordered]
    have expected : (⟨row.ordinal,target.keys,.requiredCycle⟩ : G05CandidateRow487 n) = row := by
      cases row
      simp_all
    have yes : readG05LocalMark487 check j row.ordinal d bit none = some .requiredCycle := by
      rw [value]
      rfl
    rw [yes]
    exact congrArg some expected
  | nonrecursive v =>
    rw [mark] at explained
    have value : bit = false := by
      cases bit with
      | false => rfl
      | true => exact False.elim (explained.1 (meaningBit.mp rfl))
    obtain ⟨data,parsed⟩ := localComplete i.val row.ordinal d v explained.2
    refine ⟨some data,?_⟩
    rw [Nat.zero_add,readG05OneRow487]
    simp only [sourceRead,bind,Option.bind]
    rw [ite_eq_left ordered]
    have expected : (⟨row.ordinal,target.keys,.nonrecursive v⟩ : G05CandidateRow487 n) = row := by
      cases row
      simp_all
    have yes : readG05LocalMark487 check j row.ordinal d bit (some data) = some (.nonrecursive v) := by
      rw [value]
      exact (a_local_nonrecursive_mark_requires_a_real_local_receipt_not_failed_read487).mpr
        ⟨rfl,data,rfl,parsed⟩
    rw [yes]
    exact congrArg some expected

/-- A finite reification result for reports using the generator's exact
visit order. The stronger named target also asks for arbitrary exact reports. -/
theorem g05_canonical_exact_report_reifies_under_the_named_visit_and_local_protocols487
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool) (check : G05LocalChecker487)
    (Allowed : Nat → CandidateVisitKey485 n → Prop) (meaning : G05LocalMeaning487)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (protocol : G05ExactLocalProtocol487 check meaning)
    (arity : ∀ (i : Nat) (d : Declaration), (visible485 p)[i]? = some d →
      d.head.length = p.old.root.demand.arguments.length)
    (r : G05Report487 n)
    (exact : G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r)
    (canonicalOrder : ∀ computed,
      compileScopedRoster487 p gd pos rel (computedOriginalPalette486 p.old.state.core pos rel)
        coords permit = some computed →
      ∀ (i : Nat) (a : G05CandidateRow487 n) (c : ComputedOriginalCandidate486 n),
        r.rows[i]? = some a → computed[i]? = some c → a.observed = c.keys) :
    ∃ wire : G05FiniteWitness487 n, wire.roots.map Checkpoint.which = coords ∧
      checkFlatWithG05Tag487 p gd pos rel coords permit check (.inr r) (.inr wire) = true := by
  obtain ⟨lawful,coherence,root,guard,starts⟩ := scope
  obtain ⟨nodes,generatedNodes,coordinate⟩ :=
    given_exact_old_guarded_safe_roots_the_computer_returns_all_in_same_order487 root guard
  have verifiedNodes : requestRootCheck p pos rel nodes = true :=
    computed_original_roots_pass_unmodified_ordered_request_root_check487 _ _ _ _ _ generatedNodes
  have nodeCount : nodes.length = p.old.root.demand.arguments.length := by
    simpa only [List.length_map] using (all_checked_request_roots_carry_guards_and_exact_list_length487 verifiedNodes).1
  let palette := computedOriginalPalette486 p.old.state.core pos rel
  have complete : CompletePalette486 p.old.state.core pos rel palette :=
    real_existing_graph_finitely_computes_its_verified_optional_palette486 _ _ _
  obtain ⟨computed,signs,stage,checked,_⟩ :=
    independently_scoped_all_canonical_head_coordinates_produce_a_rechecked_whole_tape486
      p gd pos rel palette complete nodes permit Allowed (fun ord key => (lawful ord key).mp)
      verifiedNodes nodeCount arity (fun i j site atSource => starts i j site (by simpa only [coordinate] using atSource))
  have identical := scoped_roster_reproduces_the_exact_old_packets_in_original_visible_order487
    (gd := gd) complete coords permit guard coherence
  have compiled : compileScopedRoster487 p gd pos rel palette coords permit = some computed := by
    rw [identical]
    simpa only [coordinate] using stage
  obtain ⟨tokens,assembled⟩ := a_signed_tape_and_exact_canonical_local_reports_supply_finite_checked_tokens487
    compiled checked Allowed lawful exact (canonicalOrder computed compiled) protocol.2
  let wire : G05FiniteWitness487 n := ⟨nodes,computed.map (fun row => (row.authoredOrdinal,row.packet)),tokens⟩
  refine ⟨wire,coordinate,new_tag_check_succeeds_iff_it_replays_the_same_full_report_data487.mpr ?_⟩
  have expected : (⟨r.rows,G05PriorityOfRows487 r.rows⟩ : G05Report487 n) = r := by
    cases r
    simp_all [G05ExactCandidateReport487]
  have replay : readG05ScopedReport487 p gd pos rel coords permit check wire =
      some ⟨r.rows,G05PriorityOfRows487 r.rows⟩ := by
    have old : (decide (wire.roots.map Checkpoint.which = coords) && requestRootCheck p pos rel wire.roots) = true :=
      Bool.and_eq_true_iff.mpr ⟨decide_eq_true coordinate,verifiedNodes⟩
    rw [readG05ScopedReport487,ite_eq_left old]
    simp [wire,compiled,checked,assembled,Option.bind,palette]
  exact replay.trans (congrArg some expected)

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
