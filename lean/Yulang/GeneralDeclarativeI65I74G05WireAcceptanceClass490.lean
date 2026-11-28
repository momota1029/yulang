import Yulang.GeneralDeclarativeI65I74G05ReceiptOnlyReportReplay490
import Yulang.GeneralDeclarativeI65I74G05ExactReportUniqueness488
import Yulang.GeneralDeclarativeI65I74G05DeferredEntry489

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

theorem g05_report_row_equivalence_is_symmetric490 {n : Nat} {a b : List (G05CandidateRow487 n)}
    (same : g05ReportRowsEquivalent488 a b = true) :
    g05ReportRowsEquivalent488 b a = true := by
  obtain ⟨len,slots⟩ := g05ReportRowsEquivalent_preserves_all_slots_and_individual_key_coverage488 same
  refine indexed_ordinal_mark_and_visit_membership_reify_report_equivalence488 len.symm ?_
  intro j row other atRow atOther
  obtain ⟨known,atKnown,ord,mark,keys⟩ := slots j other atOther
  have identified := Option.some.inj (atKnown.symm.trans atRow)
  subst known
  exact ⟨ord.symm,mark.symm,fun key => (keys key).symm⟩

theorem g05_report_row_equivalence_is_transitive490 {n : Nat} {a b c : List (G05CandidateRow487 n)}
    (ab : g05ReportRowsEquivalent488 a b = true) (bc : g05ReportRowsEquivalent488 b c = true) :
    g05ReportRowsEquivalent488 a c = true := by
  obtain ⟨lenAB,slotsAB⟩ := g05ReportRowsEquivalent_preserves_all_slots_and_individual_key_coverage488 ab
  obtain ⟨lenBC,slotsBC⟩ := g05ReportRowsEquivalent_preserves_all_slots_and_individual_key_coverage488 bc
  refine indexed_ordinal_mark_and_visit_membership_reify_report_equivalence488 (lenAB.trans lenBC) ?_
  intro j row fromC atRow atC
  obtain ⟨mid,atMid,ordAB,markAB,keysAB⟩ := slotsAB j row atRow
  obtain ⟨endRow,atEnd,ordBC,markBC,keysBC⟩ := slotsBC j mid atMid
  have actual := Option.some.inj (atEnd.symm.trans atC)
  subst endRow
  exact ⟨ordAB.trans ordBC,markAB.trans markBC,fun key => (keysAB key).trans (keysBC key)⟩

/-- Equality of candidate order, marks and visit membership, with the
same priority. Only the serialization inside each visit list is ignored. -/
def G05SameWireReportClass490 {n : Nat} (a b : G05Report487 n) : Prop :=
  g05ReportRowsEquivalent488 a.rows b.rows = true ∧ a.priority = b.priority

private def acceptG05FromReplay490 {n : Nat} (known : Option (G05Report487 n)) (r : G05Report487 n) : Bool :=
  match known with
  | none => false
  | some canonical =>
    g05ReportRowsEquivalent488 canonical.rows r.rows && decide (r.priority = G05PriorityOfRows487 r.rows)

private theorem a_known_successful_g05_replay_selects_one_exact_report_class490
    {n : Nat} {known : Option (G05Report487 n)} {a b : G05Report487 n}
    (acceptA : acceptG05FromReplay490 known a = true) :
    acceptG05FromReplay490 known b = true ↔ G05SameWireReportClass490 a b := by
  cases known with
  | none => simp [acceptG05FromReplay490] at acceptA
  | some canonical =>
    simp only [acceptG05FromReplay490,Bool.and_eq_true,decide_eq_true_eq] at acceptA ⊢
    constructor
    · rintro ⟨acceptB,priorityB⟩
      have equivalent := g05_report_row_equivalence_is_transitive490
        (g05_report_row_equivalence_is_symmetric490 acceptA.1) acceptB
      have samePrio := equivalent_g05_report_rows_keep_the_same_priority_without_comparing_their_observation_lists488 equivalent
      exact ⟨equivalent,acceptA.2.trans (samePrio.trans priorityB.symm)⟩
    · rintro ⟨equivalent,samePrio⟩
      have rows := equivalent_g05_report_rows_keep_the_same_priority_without_comparing_their_observation_lists488 equivalent
      exact ⟨g05_report_row_equivalence_is_transitive490 acceptA.1 equivalent,
        samePrio.symm.trans (acceptA.2.trans rows)⟩

theorem for_one_accepted_g05_wire_every_other_report_accepts_iff_it_is_the_same_exact_report_class490
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {test : G05LocalChecker487}
    {wire : G05FiniteWitness487 n} {a b : G05Report487 n}
    (acceptA : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr a) (.inr wire) = true) :
    checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit test (.inr b) (.inr wire) = true ↔
      G05SameWireReportClass490 a b := by
  cases coords with
  | nil =>
    exact a_known_successful_g05_replay_selects_one_exact_report_class490
      (known := readNoArgumentG05Report488 p gd pos rel permit test wire) acceptA
  | cons first rest =>
    exact a_known_successful_g05_replay_selects_one_exact_report_class490
      (known := readG05ScopedReport487 p gd pos rel (first::rest) permit test wire) acceptA

theorem a_lawful_g05_receipt_translation_preserves_the_acceptance_bool_of_all_report_serializations490
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {left right : G05LocalChecker487} {translate : G05TokenMap490}
    {wire : G05FiniteWitness487 n} {a : G05Report487 n}
    (lawful : G05TokenMapPreservesDecoded490 left right translate)
    (acceptA : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit left (.inr a) (.inr wire) = true) :
    ∃ out, translateG05WitnessTokens490 p left translate wire = some out ∧
      out.roots = wire.roots ∧ out.tape = wire.tape ∧
      ∀ b : G05Report487 n,
        checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit left (.inr b) (.inr wire) =
        checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit right (.inr b) (.inr out) := by
  obtain ⟨out,mapped,roots,tape,again⟩ :=
    a_usable_g05_token_map_outputs_an_accepted_wire_with_exactly_the_same_roots_and_candidate_tape490 lawful acceptA
  refine ⟨out,mapped,roots,tape,?_⟩
  intro b
  have same := (for_one_accepted_g05_wire_every_other_report_accepts_iff_it_is_the_same_exact_report_class490
    (b := b) acceptA).trans
    (for_one_accepted_g05_wire_every_other_report_accepts_iff_it_is_the_same_exact_report_class490
      (b := b) again).symm
  exact Bool.eq_iff_iff.mpr same

/-- After translating a verified wire, the unchanged deferred router
has exactly the same behavior on any submitted report, not just the report
that established the wire was valid. -/
theorem g05_token_only_translation_preserves_every_deferred_outcome_with_that_wire490
    {n : Nat} {α : Type} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {left right : G05LocalChecker487} {translate : G05TokenMap490}
    {wire : G05FiniteWitness487 n} {a : G05Report487 n}
    (lawful : G05TokenMapPreservesDecoded490 left right translate)
    (acceptA : checkFlatWithDemandScopedG05Tag488 p gd pos rel coords permit left (.inr a) (.inr wire) = true) :
    ∃ out, translateG05WitnessTokens490 p left translate wire = some out ∧
      out.roots = wire.roots ∧ out.tape = wire.tape ∧
      ∀ (b : G05Report487 n) (next : List (Nat × G05LocalVerdict487) → α),
        routeG05WithDeferredLocal489 p gd pos rel coords permit left (fun _ => some (b,wire)) next =
        routeG05WithDeferredLocal489 p gd pos rel coords permit right (fun _ => some (b,out)) next := by
  obtain ⟨out,mapped,roots,tape,unchanged⟩ :=
    a_lawful_g05_receipt_translation_preserves_the_acceptance_bool_of_all_report_serializations490 lawful acceptA
  refine ⟨out,mapped,roots,tape,?_⟩
  intro b next
  have full :
      routeFromCheckedG05Report488 p gd pos rel coords permit left b wire next =
      routeFromCheckedG05Report488 p gd pos rel coords permit right b out next := by
    unfold routeFromCheckedG05Report488
    rw [unchanged b]
  unfold routeG05WithDeferredLocal489
  cases visit : readG05Preflight489 p gd pos rel coords permit with
  | none => exact full
  | some result =>
    cases result with
    | recursive => rfl
    | allSafe => exact full

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
