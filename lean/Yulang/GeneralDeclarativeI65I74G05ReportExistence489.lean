import Yulang.GeneralDeclarativeI65I74G05DeferredBoundary489

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint)

def G05NonrecursiveVerdictAvailable489 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (Allowed : Nat → CandidateVisitKey485 n → Prop) (meaning : G05LocalMeaning487) : Prop :=
  ∀ (i : Fin (visible485 p).length) ord d, OriginalRosterCell485 p i.val (ord,d) →
    ¬IndependentScopedReturn487 p gd pos rel coords Allowed i.val →
    ∃ v, meaning i.val ord d v

private theorem exact_g05_footprint_exists_for_every_original_index489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {Allowed : Nat → CandidateVisitKey485 n → Prop}
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed) :
    ∀ i : Fin (visible485 p).length, ∃ ord d keys, OriginalRosterCell485 p i.val (ord,d) ∧
      G05OriginalVisitsExact487 p gd pos rel coords i.val (Allowed ord) keys := by
  cases coords with
  | nil =>
    intro i
    obtain ⟨⟨ord,d⟩,known⟩ := no_visible_slot_is_lost_in_the_exact_roster485 p i
    exact ⟨ord,d,[],(roster_cell_reads_exactly_its_two_original_slots485 ..).mp known,
      fun key => by simp⟩
  | cons first rest =>
    have nonempty : first::rest ≠ [] := List.cons_ne_nil _ _
    obtain ⟨out,replayed⟩ := original_nonempty_g05_demand_replays_full_preflight_without_any_local_receipts489
      p gd pos rel (first::rest) permit Allowed scope nonempty
    unfold readG05Preflight489 at replayed
    cases made : computedOriginalRootCertificates487 p.old.state.core pos rel
        (p.old.root.demand.arguments.map (·.lower)) with
    | none => simp [made] at replayed
    | some roots =>
      simp only [made,bind,Option.bind] at replayed
      split at replayed
      · rename_i coord
        obtain ⟨_,computed,finished,_⟩ := scoped_election_checks_unchanged_safe_original_roots_and_full_packet_tape487 replayed
        rw [coord] at finished
        intro i
        obtain ⟨row,d,_,identity,_,each⟩ :=
          successful_scoped_roster_reads_every_actual_visible_slot_and_its_exact_independent_visits487 finished i Allowed scope.1
        refine ⟨row.authoredOrdinal,d,row.keys,identity,fun key => ?_⟩
        constructor
        · intro member
          obtain ⟨root,arg,atRoot,head,visited⟩ := (each key).mp member
          exact ⟨arg,root,atRoot,head,visited⟩
        · rintro ⟨arg,root,atRoot,head,visited⟩
          exact (each key).mpr ⟨root,arg,atRoot,head,visited⟩
      · cases replayed

theorem existence_of_an_independently_exact_g05_report_is_equivalent_to_local_verdict_availability489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool}
    {Allowed : Nat → CandidateVisitKey485 n → Prop} {meaning : G05LocalMeaning487}
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed) :
    (∃ r, G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r) ↔
      G05NonrecursiveVerdictAvailable489 p gd pos rel coords Allowed meaning := by
  classical
  constructor
  · rintro ⟨r,exactReport⟩ i ord d original safe
    obtain ⟨row,e,_,identity,_,mark⟩ := exactReport.2.2 i
    have same := Option.some.inj
      (((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr identity).symm.trans
        ((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr original))
    cases status : row.mark with
    | requiredCycle =>
      rw [status] at mark
      exact False.elim (safe mark)
    | nonrecursive v =>
      rw [status] at mark
      obtain ⟨sameOrd,sameDecl⟩ := Prod.mk.inj same
      exact ⟨v,sameOrd ▸ sameDecl ▸ mark.2⟩
  · intro available
    have localRows : ∀ i : Fin (visible485 p).length, ∃ (row : G05CandidateRow487 n) (d : GeneralDeclarations.Declaration),
        OriginalRosterCell485 p i.val (row.ordinal,d) ∧
        G05OriginalVisitsExact487 p gd pos rel coords i.val (Allowed row.ordinal) row.observed ∧
        match row.mark with
        | .requiredCycle => IndependentScopedReturn487 p gd pos rel coords Allowed i.val
        | .nonrecursive v =>
          ¬IndependentScopedReturn487 p gd pos rel coords Allowed i.val ∧ meaning i.val row.ordinal d v := by
      intro i
      obtain ⟨ord,d,keys,roster,visits⟩ := exact_g05_footprint_exists_for_every_original_index489 scope i
      by_cases cyclic : IndependentScopedReturn487 p gd pos rel coords Allowed i.val
      · exact ⟨⟨ord,keys,.requiredCycle⟩,d,roster,visits,cyclic⟩
      · obtain ⟨v,matchLocal⟩ := available i ord d roster cyclic
        exact ⟨⟨ord,keys,.nonrecursive v⟩,d,roster,visits,cyclic,matchLocal⟩
    let chosen := fun i => Classical.choose (localRows i)
    let rows := List.ofFn chosen
    refine ⟨⟨rows,G05PriorityOfRows487 rows⟩,rfl,List.length_ofFn,?_⟩
    intro i
    have atPosition : rows[i.val]? = some (chosen i) := by
      simp [rows,i.isLt]
    obtain ⟨d,entry,visits,verdict⟩ := Classical.choose_spec (localRows i)
    exact ⟨chosen i,d,atPosition,entry,visits,verdict⟩

theorem a_replayable_exact_g05_report_exists_iff_every_nonrecursive_slot_has_some_local_verdict489
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool)
    (test : G05LocalChecker487) (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (meaning : G05LocalMeaning487)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (protocol : G05ExactLocalProtocol487 test meaning) :
    (∃ r w, checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inr w) = true) ↔
      G05NonrecursiveVerdictAvailable489 p gd pos rel coords Allowed meaning := by
  constructor
  · rintro ⟨r,w,checked⟩
    have full := (verified_g05_report_has_exact_original_coordinates_and_evidence_for_all_fitting_models488
      Allowed scope meaning protocol (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ _ => True.intro) checked).2.1
    exact (existence_of_an_independently_exact_g05_report_is_equivalent_to_local_verdict_availability489 scope).mp
      ⟨r,full⟩
  · intro available
    obtain ⟨r,full⟩ := (existence_of_an_independently_exact_g05_report_is_equivalent_to_local_verdict_availability489 scope).mpr
      available
    obtain ⟨wire,_,checked⟩ := independently_exact_g05_reports_reify_without_an_observation_order_or_arity_assumption488
      p gd pos rel coords permit test Allowed meaning scope protocol r full
    exact ⟨r,wire,checked⟩

theorem an_actual_k2_refuses_before_an_unclassified_safe_rival_can_supply_any_full_report489
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (permit : Nat → CandidateVisitKey485 n → Bool)
    (test : G05LocalChecker487) (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (meaning : G05LocalMeaning487)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (protocol : G05ExactLocalProtocol487 test meaning)
    (nonempty : coords ≠ []) (genuine safeRival : Fin (visible485 p).length)
    (cycle : IndependentScopedReturn487 p gd pos rel coords Allowed genuine.val)
    (safe : ¬ IndependentScopedReturn487 p gd pos rel coords Allowed safeRival.val)
    (ordinal : Nat) (d : GeneralDeclarations.Declaration)
    (original : OriginalRosterCell485 p safeRival.val (ordinal,d))
    (noVerdict : ∀ v, ¬ meaning safeRival.val ordinal d v) :
    (¬ ∃ r w, checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr r) (.inr w) = true) ∧
      ∃ hits, readG05Preflight489 p gd pos rel coords permit = some (.recursive hits) := by
  constructor
  · intro full
    have need := (a_replayable_exact_g05_report_exists_iff_every_nonrecursive_slot_has_some_local_verdict489
      p gd pos rel coords permit test Allowed meaning scope protocol).mp full
    obtain ⟨v,proof⟩ := need safeRival ordinal d original safe
    exact noVerdict v proof
  · obtain ⟨hits,ran,_⟩ := a_real_independent_g05_k2_on_nonempty_original_demand_replays_without_any_local_matcher489
      p gd pos rel coords permit Allowed scope nonempty genuine cycle
    exact ⟨hits,ran⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
