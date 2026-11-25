import Yulang.GeneralDeclarativeI65I72GroundedBodyAssembly405

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

private theorem exact_succ_read405 {p : Option Nat} {n : Nat} :
    p.map Nat.succ = some n → ∃ i, p = some i ∧ n = i+1 := by
  cases p <;> simp [eq_comm]

/-- Visibility is a stable filter of the actual registry. Two covered
visible ordinals cannot reverse when mapped back to raw source
declarations; this does not use distinct impl IDs. -/
theorem unfilter_keeps_original_order405 {α : Type} (test : α → Bool) (rows : List α)
    {i j a b : Nat} (ordered : i < j)
    (left : unfilterOrdinal395 test rows i = some a)
    (right : unfilterOrdinal395 test rows j = some b) : a < b := by
  induction rows generalizing i j a b with
  | nil => simp [unfilterOrdinal395] at left
  | cons h t ih =>
    cases pass : test h with
    | false =>
      have la : (unfilterOrdinal395 test t i).map Nat.succ = some a := by
        simpa [unfilterOrdinal395,pass] using left
      have ra : (unfilterOrdinal395 test t j).map Nat.succ = some b := by
        simpa [unfilterOrdinal395,pass] using right
      obtain ⟨l,atL,al⟩ := exact_succ_read405 la
      obtain ⟨r,atR,br⟩ := exact_succ_read405 ra
      rw [al,br]
      exact Nat.succ_lt_succ (ih ordered atL atR)
    | true =>
      cases j with
      | zero => omega
      | succ j =>
        have ra : (unfilterOrdinal395 test t j).map Nat.succ = some b := by
          simpa [unfilterOrdinal395,pass] using right
        obtain ⟨r,atR,br⟩ := exact_succ_read405 ra
        cases i with
        | zero =>
          have a0 : a = 0 := by simpa [unfilterOrdinal395,pass,eq_comm] using left
          rw [a0,br]
          exact Nat.zero_lt_succ _
        | succ i =>
          have la : (unfilterOrdinal395 test t i).map Nat.succ = some a := by
            simpa [unfilterOrdinal395,pass] using left
          obtain ⟨l,atL,al⟩ := exact_succ_read405 la
          rw [al,br]
          exact Nat.succ_lt_succ (ih (Nat.lt_of_succ_lt_succ ordered) atL atR)

theorem native_visits_do_not_reorder_visible_declarations405 {s q l r needL needR}
    (first : NativeEntryAddress405 s q l needL)
    (later : NativeEntryAddress405 s q r needR)
    (order : first.visibleOrdinal < later.visibleOrdinal) :
    first.site.declarationOrdinal < later.site.declarationOrdinal :=
  unfilter_keeps_original_order405 (fun row : Declaration => row.role == q.demand.role)
    (authoredRegistry s.core.current).declarations order first.fromVisible later.fromVisible

theorem native_address_cannot_switch_raw_row_at_same_ordinal405 {s q l r needL needR}
    (a : NativeEntryAddress405 s q l needL) (b : NativeEntryAddress405 s q r needR)
    (same : a.visibleOrdinal = b.visibleOrdinal) :
    a.site.declarationOrdinal = b.site.declarationOrdinal ∧ l = r := by
  have i := a.fromVisible
  rw [same,b.fromVisible] at i
  have row := a.visitedRow
  rw [same,b.visitedRow] at row
  exact ⟨Option.some.inj i.symm,Option.some.inj row.symm⟩

end Yulang.GeneralDeclarativeI65.I72
