import Yulang.GeneralDeclarativeI65I74G05ExactPriority488

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

def G05LocalMeaningSingleValued488 (rule : G05LocalMeaning487) : Prop :=
  ∀ i ord declaration a b, rule i ord declaration a → rule i ord declaration b → a = b

theorem equivalent_g05_report_rows_keep_the_same_priority_without_comparing_their_observation_lists488
    {n : Nat} {a b : List (G05CandidateRow487 n)}
    (equivalent : g05ReportRowsEquivalent488 a b = true) :
    G05PriorityOfRows487 a = G05PriorityOfRows487 b := by
  apply same_ordered_marks_imply_same_prioritized_g05_scope488
  induction a generalizing b with
  | nil => cases b <;> simp_all [g05ReportRowsEquivalent488,g05RowMarkPairs488]
  | cons a rest ih =>
    cases b with
    | nil => simp [g05ReportRowsEquivalent488] at equivalent
    | cons b next =>
      obtain ⟨first,later⟩ := Bool.and_eq_true_iff.mp equivalent
      have parts : ((decide (a.ordinal = b.ordinal) && decide (a.mark = b.mark)) &&
        g05VisitMembershipEqual488 a.observed b.observed) = true := first
      obtain ⟨ids,marks⟩ := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp parts).1
      have ix : a.ordinal = b.ordinal := of_decide_eq_true ids
      have state : a.mark = b.mark := of_decide_eq_true marks
      change (a.ordinal,a.mark)::g05RowMarkPairs488 rest =
        (b.ordinal,b.mark)::g05RowMarkPairs488 next
      rw [ix,state,ih later]

theorem exact_g05_reports_have_the_same_membership_marks_and_priority_if_the_local_rule_is_single_valued488
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {Allowed : Nat → CandidateVisitKey485 n → Prop} {rule : G05LocalMeaning487}
    {a b : G05Report487 n}
    (first : G05ExactCandidateReport487 p gd pos rel coords Allowed rule a)
    (second : G05ExactCandidateReport487 p gd pos rel coords Allowed rule b)
    (unique : G05LocalMeaningSingleValued488 rule) :
    g05ReportRowsEquivalent488 a.rows b.rows = true ∧ a.priority = b.priority := by
  have result : g05ReportRowsEquivalent488 a.rows b.rows = true := by
    apply indexed_ordinal_mark_and_visit_membership_reify_report_equivalence488
      (first.2.1.trans second.2.1.symm)
    intro j x y hx hy
    let i : Fin (visible485 p).length :=
      ⟨j,first.2.1 ▸ (List.getElem?_eq_some_iff.mp hx).1⟩
    obtain ⟨aRow,d,atA,cellA,visitsA,markA⟩ := first.2.2 i
    obtain ⟨bRow,e,atB,cellB,visitsB,markB⟩ := second.2.2 i
    have eqA : aRow = x := Option.some.inj (atA.symm.trans hx)
    have eqB : bRow = y := Option.some.inj (atB.symm.trans hy)
    subst aRow
    subst bRow
    have identity : (x.ordinal,d) = (y.ordinal,e) := Option.some.inj
      (((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr cellA).symm.trans
        ((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr cellB))
    have ord : x.ordinal = y.ordinal := congrArg Prod.fst identity
    have decl : d = e := congrArg Prod.snd identity
    refine ⟨ord,?_,?_⟩
    · cases aMark : x.mark <;> cases bMark : y.mark
      · rfl
      · rw [aMark] at markA
        rw [bMark] at markB
        exact False.elim (markB.1 markA)
      · rw [aMark] at markA
        rw [bMark] at markB
        exact False.elim (markA.1 markB)
      · rename_i v w
        rw [aMark] at markA
        rw [bMark] at markB
        have ma : rule i.val y.ordinal e v := by simpa only [ord,decl] using markA.2
        exact congrArg G05CandidateMark487.nonrecursive (unique i.val y.ordinal e v w ma markB.2)
    · intro key
      have aKeys := visitsA key
      rw [ord] at aKeys
      exact aKeys.trans (visitsB key).symm
  exact ⟨result,first.1.trans
    ((equivalent_g05_report_rows_keep_the_same_priority_without_comparing_their_observation_lists488 result).trans second.1.symm)⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
