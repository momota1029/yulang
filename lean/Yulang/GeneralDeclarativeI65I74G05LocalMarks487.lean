import Yulang.GeneralDeclarativeI65I74G05Goal487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open GeneralDeclarations (Declaration)

def readG05LocalMark487 (check : G05LocalChecker487) (i ordinal : Nat) (d : Declaration) :
    Bool → Option (List Nat) → Option G05CandidateMark487
  | true,none => some .requiredCycle
  | false,some wire => (check i ordinal d wire).map G05CandidateMark487.nonrecursive
  | _,_ => none

def readG05OneRow487 {n : Nat} (p : FullProblem) (check : G05LocalChecker487)
    (i : Nat) (candidate : ComputedOriginalCandidate486 n) (signed : Nat × Bool)
    (localToken : Option (List Nat)) : Option (G05CandidateRow487 n) := do
  let (ordinal,d) ← rosterCell485 p i
  if ordinal = signed.1 && ordinal = candidate.authoredOrdinal && i = candidate.packet.visibleOrdinal then
    let mark ← readG05LocalMark487 check i ordinal d signed.2 localToken
    pure ⟨ordinal,candidate.keys,mark⟩
  else none

def readG05OrderedRows487 {n : Nat} (p : FullProblem) (check : G05LocalChecker487) :
    Nat → List (ComputedOriginalCandidate486 n) → List (Nat × Bool) → List (Option (List Nat)) →
      Option (List (G05CandidateRow487 n))
  | _,[],[],[] => some []
  | i,candidate::remaining,sign::later,token::other => do
    let row ← readG05OneRow487 p check i candidate sign token
    let rows ← readG05OrderedRows487 p check (i+1) remaining later other
    pure (row :: rows)
  | _,_,_,_ => none

theorem a_local_k2_mark_is_exactly_a_checked_true_bit_and_no_local_selection_token487
    {check : G05LocalChecker487} {i ordinal : Nat} {d : Declaration}
    {sign : Bool} {token : Option (List Nat)} :
    readG05LocalMark487 check i ordinal d sign token = some .requiredCycle ↔
      sign = true ∧ token = none := by
  cases token with
  | none => cases sign <;> simp [readG05LocalMark487]
  | some w =>
    cases sign with
    | true => simp [readG05LocalMark487]
    | false => cases check i ordinal d w <;> simp [readG05LocalMark487]

theorem a_local_nonrecursive_mark_requires_a_real_local_receipt_not_failed_read487
    {check : G05LocalChecker487} {i ordinal : Nat} {d : Declaration}
    {sign : Bool} {token : Option (List Nat)} {v : G05LocalVerdict487} :
    readG05LocalMark487 check i ordinal d sign token = some (.nonrecursive v) ↔
      sign = false ∧ ∃ w, token = some w ∧ check i ordinal d w = some v := by
  cases token with
  | none => cases sign <;> simp [readG05LocalMark487]
  | some w =>
    cases sign with
    | true => simp [readG05LocalMark487]
    | false => cases check i ordinal d w <;> simp [readG05LocalMark487]

theorem new_g05_row_preserves_original_slot_signed_bit_observed_keys_and_actual_local_mark487
    {n : Nat} {p : FullProblem} {check : G05LocalChecker487} {i : Nat}
    {candidate : ComputedOriginalCandidate486 n} {signed : Nat × Bool}
    {localToken : Option (List Nat)} {row : G05CandidateRow487 n}
    (ran : readG05OneRow487 p check i candidate signed localToken = some row) :
    ∃ d, OriginalRosterCell485 p i (row.ordinal,d) ∧
      row.ordinal = signed.1 ∧ row.ordinal = candidate.authoredOrdinal ∧
      row.observed = candidate.keys ∧ i = candidate.packet.visibleOrdinal ∧
      readG05LocalMark487 check i row.ordinal d signed.2 localToken = some row.mark := by
  unfold readG05OneRow487 at ran
  cases original : rosterCell485 p i with
  | none => simp [original] at ran
  | some pair =>
    obtain ⟨ord,d⟩ := pair
    simp only [original,bind,Option.bind] at ran
    split at ran
    · rename_i approved
      obtain ⟨seat,head⟩ := Bool.and_eq_true_iff.mp approved
      obtain ⟨sg,roster⟩ := Bool.and_eq_true_iff.mp seat
      cases marked : readG05LocalMark487 check i ord d signed.2 localToken with
      | none => simp [marked] at ran
      | some mark =>
        have same : (⟨ord,candidate.keys,mark⟩ : G05CandidateRow487 n) = row :=
          Option.some.inj (by simpa [marked] using ran)
        subst row
        exact ⟨d,(roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mp original,
          of_decide_eq_true sg,of_decide_eq_true roster,rfl,of_decide_eq_true head,marked⟩
    · cases ran

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
