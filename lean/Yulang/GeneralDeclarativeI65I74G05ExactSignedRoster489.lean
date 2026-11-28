import Yulang.GeneralDeclarativeI65I74G05ExactPriority488

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint)

/-- The signs are independent of report serialization, local receipts and
election. They are indexed by the complete original visible roster. -/
def G05ExactSignedRoster489 (p : FullProblem) (recurs : Nat → Prop)
    (bits : List (Nat × Bool)) : Prop :=
  bits.length = (visible485 p).length ∧
  ∀ i : Fin (visible485 p).length, ∃ ord d flag,
    OriginalRosterCell485 p i.val (ord,d) ∧ bits[i.val]? = some (ord,flag) ∧
      (flag = true ↔ recurs i.val)

theorem exact_g05_signed_roster_is_unique_in_original_order489
    {p : FullProblem} {recurs : Nat → Prop} {a b : List (Nat × Bool)}
    (first : G05ExactSignedRoster489 p recurs a) (second : G05ExactSignedRoster489 p recurs b) :
    a = b := by
  apply List.ext_getElem?
  intro j
  by_cases bound : j < (visible485 p).length
  · let i : Fin (visible485 p).length := ⟨j,bound⟩
    obtain ⟨aOrd,aDecl,aFlag,aOld,aHere,aExact⟩ := first.2 i
    obtain ⟨bOrd,bDecl,bFlag,bOld,bHere,bExact⟩ := second.2 i
    have sameOrd : aOrd = bOrd := congrArg Prod.fst (Option.some.inj
      (((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr aOld).symm.trans
        ((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr bOld)))
    have sameFlag : aFlag = bFlag := by
      cases aFlag <;> cases bFlag
      · rfl
      · cases aExact.mpr (bExact.mp rfl)
      · cases bExact.mpr (aExact.mp rfl)
      · rfl
    change a[i.val]? = b[i.val]?
    rw [aHere,bHere,sameOrd,sameFlag]
  · have aBound : a.length ≤ j := by simpa only [first.1] using Nat.le_of_not_gt bound
    have bBound : b.length ≤ j := by simpa only [second.1] using Nat.le_of_not_gt bound
    rw [List.getElem?_eq_none aBound,List.getElem?_eq_none bBound]

def g05SignsOfReport489 {n : Nat} (r : G05Report487 n) : List (Nat × Bool) :=
  r.rows.map (fun x => (x.ordinal,decide (x.mark = .requiredCycle)))

theorem independent_full_g05_report_has_exact_original_signed_roster489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {Allowed : Nat → CandidateVisitKey485 n → Prop} {meaning : G05LocalMeaning487}
    {r : G05Report487 n}
    (exactReport : G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r) :
    G05ExactSignedRoster489 p (IndependentScopedReturn487 p gd pos rel coords Allowed)
      (g05SignsOfReport489 r) := by
  refine ⟨by simpa only [g05SignsOfReport489,List.length_map] using exactReport.2.1,?_⟩
  intro i
  obtain ⟨row,d,atRow,origin,_,classified⟩ := exactReport.2.2 i
  refine ⟨row.ordinal,d,decide (row.mark = .requiredCycle),origin,?_,?_⟩
  · simp only [g05SignsOfReport489,List.getElem?_map,atRow,Option.map_some]
  · rw [decide_eq_true_eq]
    cases mark : row.mark with
    | requiredCycle =>
      rw [mark] at classified
      simp [classified]
    | nonrecursive v =>
      rw [mark] at classified
      simp [classified.1]

theorem positive_signs_of_g05_report_are_its_whole_original_ordered_hit_list489
    {n : Nat} (r : G05Report487 n) :
    positiveOrdinals485 (g05SignsOfReport489 r) = reportedOriginalG05Cycles488 r.rows := by
  change positiveOrdinals485 (r.rows.map fun x => (x.ordinal,decide (x.mark = .requiredCycle))) =
    reportedOriginalG05Cycles488 r.rows
  induction r.rows with
  | nil => rfl
  | cons next rest ih =>
    cases h : next.mark with
    | requiredCycle =>
      simp only [positiveOrdinals485,reportedOriginalG05Cycles488] at ih ⊢
      simp [h,ih]
    | nonrecursive v =>
      simp only [positiveOrdinals485,reportedOriginalG05Cycles488] at ih ⊢
      simp [h,ih]

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
