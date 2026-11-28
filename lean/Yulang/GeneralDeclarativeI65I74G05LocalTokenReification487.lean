import Yulang.GeneralDeclarativeI65I74G05ReportSound487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)

theorem exact_locally_available_marks_reify_one_finite_ordered_local_receipt_list487
    {n : Nat} (p : FullProblem) (check : G05LocalChecker487) (offset : Nat)
    (computed : List (ComputedOriginalCandidate486 n)) (signed : List (Nat × Bool))
    (rows : List (G05CandidateRow487 n))
    (countC : computed.length = rows.length) (countS : signed.length = rows.length)
    (available : ∀ j candidate bit row,
      computed[j]? = some candidate → signed[j]? = some bit → rows[j]? = some row →
      ∃ token, readG05OneRow487 p check (offset+j) candidate bit token = some row) :
    ∃ tokens, readG05OrderedRows487 p check offset computed signed tokens = some rows := by
  induction rows generalizing offset computed signed with
  | nil =>
    have emptyC : computed = [] := List.length_eq_zero_iff.mp countC
    have emptyS : signed = [] := List.length_eq_zero_iff.mp countS
    subst computed
    subst signed
    exact ⟨[],rfl⟩
  | cons row tail ih =>
    cases computed with
    | nil => simp at countC
    | cons front rest =>
      cases signed with
      | nil => simp at countS
      | cons bit bits =>
        obtain ⟨token,read⟩ := available 0 front bit row rfl rfl rfl
        have now : readG05OneRow487 p check offset front bit token = some row := by simpa using read
        obtain ⟨later,ran⟩ := ih (offset+1) rest bits
          (Nat.succ.inj countC) (Nat.succ.inj countS) (fun j c b rr continuing matched expected => by
            obtain ⟨t,proof⟩ := available (j+1) c b rr continuing matched expected
            exact ⟨t,by simpa only [Nat.add_assoc,Nat.add_comm 1 j] using proof⟩)
        exact ⟨token::later,by simp [readG05OrderedRows487,now,ran,Option.bind]⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
