import Yulang.GeneralDeclarativeI65I74G05ReportExistence489

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

abbrev G05OrderedLocalChoices490 (p : FullProblem) :=
  Fin (visible485 p).length → Nat × G05LocalVerdict487

/-- All original slots are independently nonrecursive, and the selected
verdict at each original slot satisfies the independent local rule.
No row serialization, receipt, or implementation appears here. -/
def G05OrderedSafeChoices490 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (Allowed : Nat → CandidateVisitKey485 n → Prop) (meaning : G05LocalMeaning487)
    (choices : G05OrderedLocalChoices490 p) : Prop :=
  ∀ i, ¬ IndependentScopedReturn487 p gd pos rel coords Allowed i.val ∧
    ∃ d, OriginalRosterCell485 p i.val ((choices i).1,d) ∧ meaning i.val (choices i).1 d (choices i).2

private theorem g05_ofFn_filterMap_some490 {A B : Type} {k : Nat}
    (f : Fin k → A) (g : Fin k → B) (read : A → Option B)
    (pointwise : ∀ i, read (f i) = some (g i)) :
    (List.ofFn f).filterMap read = List.ofFn g := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ,List.ofFn_succ,List.filterMap_cons,pointwise 0]
    exact congrArg (List.cons (g 0)) (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => pointwise i.succ))

/-- With a nonrecursive verdict at every index, the eligible list is
exactly the supplied list in the same order, with no suppressed positions. -/
theorem g05_priority_keeps_every_ordered_original_local_choice490
    {n k : Nat} {rows : List (G05CandidateRow487 n)} (length : rows.length = k)
    (choices : Fin k → Nat × G05LocalVerdict487)
    (matchingRows : ∀ i : Fin k, ∃ row, rows[i.val]? = some row ∧
      row.ordinal = (choices i).1 ∧ row.mark = .nonrecursive (choices i).2) :
    G05PriorityOfRows487 rows = .eligible (List.ofFn choices) := by
  let observed := fun i : Fin k => rows[i.val]'(length.symm ▸ i.isLt)
  have mirror : rows = List.ofFn observed := by
    apply List.ext_getElem?
    intro j
    by_cases bound : j < k
    · rw [List.getElem?_eq_getElem (length.symm ▸ bound),List.getElem?_ofFn]
      simp [bound,observed]
    · rw [List.getElem?_eq_none (by rw [length]; exact Nat.le_of_not_gt bound),List.getElem?_ofFn]
      simp [bound]
  have observedAt : ∀ i : Fin k,
      (observed i).ordinal = (choices i).1 ∧ (observed i).mark = .nonrecursive (choices i).2 := by
    intro i
    obtain ⟨row,atRow,ord,marked⟩ := matchingRows i
    have first : rows[i.val]? = some (observed i) := List.getElem?_eq_getElem (length.symm ▸ i.isLt)
    have eq := Option.some.inj (first.symm.trans atRow)
    exact eq ▸ ⟨ord,marked⟩
  rw [mirror]
  have noCycles : reportedOriginalG05Cycles488 (List.ofFn observed) = [] := by
    unfold reportedOriginalG05Cycles488
    apply List.filterMap_eq_nil_iff.mpr
    intro row member
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
    simp [(observedAt i).2]
  change (match reportedOriginalG05Cycles488 (List.ofFn observed) with
    | [] => G05Priority487.eligible ((List.ofFn observed).filterMap fun (row : G05CandidateRow487 n) => match row.mark with
        | .requiredCycle => none | .nonrecursive v => some (row.ordinal,v))
    | first::tail => G05Priority487.recursive (first::tail)) = _
  rw [noCycles]
  apply congrArg G05Priority487.eligible
  apply g05_ofFn_filterMap_some490
  intro i
  simp [(observedAt i).2,(observedAt i).1]

theorem every_independently_permitted_g05_safe_choice_list_has_an_exact_report490
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {Allowed : Nat → CandidateVisitKey485 n → Prop}
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (meaning : G05LocalMeaning487) (choices : G05OrderedLocalChoices490 p)
    (allowedChoices : G05OrderedSafeChoices490 p gd pos rel coords Allowed meaning choices) :
    ∃ report, G05ExactCandidateReport487 p gd pos rel coords Allowed meaning report ∧
      report.priority = .eligible (List.ofFn choices) := by
  let restricted : G05LocalMeaning487 := fun j ord d v =>
    meaning j ord d v ∧ (List.ofFn choices)[j]? = some (ord,v)
  have availability : G05NonrecursiveVerdictAvailable489 p gd pos rel coords Allowed restricted := by
    intro i ord d atD _safe
    obtain ⟨chosen,source,verdict⟩ := (allowedChoices i).2
    have same := Option.some.inj
      (((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr source).symm.trans
        ((roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr atD))
    obtain ⟨ordEq,dEq⟩ := Prod.mk.inj same
    refine ⟨(choices i).2,ordEq ▸ dEq ▸ verdict,?_⟩
    simp [i.isLt,←ordEq]
  obtain ⟨report,valid⟩ :=
    (existence_of_an_independently_exact_g05_report_is_equivalent_to_local_verdict_availability489 scope).mpr availability
  have rows : ∀ i : Fin (visible485 p).length, ∃ row d,
      report.rows[i.val]? = some row ∧
      OriginalRosterCell485 p i.val (row.ordinal,d) ∧
      G05OriginalVisitsExact487 p gd pos rel coords i.val (Allowed row.ordinal) row.observed ∧
      row.ordinal = (choices i).1 ∧ row.mark = .nonrecursive (choices i).2 ∧
      meaning i.val row.ordinal d (choices i).2 := by
    intro i
    obtain ⟨row,d,one,two,three,mark⟩ := valid.2.2 i
    cases stated : row.mark with
    | requiredCycle =>
      rw [stated] at mark
      exact False.elim ((allowedChoices i).1 mark)
    | nonrecursive v =>
      rw [stated] at mark
      have picked : (choices i) = (row.ordinal,v) := by
        apply Option.some.inj
        simpa [restricted,i.isLt] using mark.2.2
      obtain ⟨sameOrd,sameVerdict⟩ := Prod.mk.inj picked
      exact ⟨row,d,one,two,three,sameOrd.symm,by rw [sameVerdict,stated],sameVerdict ▸ mark.2.1⟩
  refine ⟨report,⟨valid.1,valid.2.1,?_⟩,?_⟩
  · intro i
    obtain ⟨row,d,atRow,atD,atVisit,_,noncycle,verdict⟩ := rows i
    exact ⟨row,d,atRow,atD,atVisit,by rw [noncycle]; exact ⟨(allowedChoices i).1,verdict⟩⟩
  · rw [valid.1]
    apply g05_priority_keeps_every_ordered_original_local_choice490 valid.2.1 choices
    intro i
    obtain ⟨row,_,atRow,_,_,ord,marked,_⟩ := rows i
    exact ⟨row,atRow,ord,marked⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
