import Yulang.GeneralDeclarativeI65I74G05LocalMarks487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)

theorem g05_ordered_rows_keep_the_entire_signed_candidate_roster487
    {n : Nat} {p : FullProblem} {check : G05LocalChecker487} {offset : Nat}
    {candidates : List (ComputedOriginalCandidate486 n)}
    {signed : List (Nat × Bool)} {tokens : List (Option (List Nat))}
    {rows : List (G05CandidateRow487 n)}
    (ran : readG05OrderedRows487 p check offset candidates signed tokens = some rows) :
    rows.length = signed.length ∧
    ∀ j (row : G05CandidateRow487 n), rows[j]? = some row →
      ∃ candidate bit token, candidates[j]? = some candidate ∧ signed[j]? = some bit ∧
        tokens[j]? = some token ∧ readG05OneRow487 p check (offset+j) candidate bit token = some row := by
  induction candidates generalizing signed tokens rows offset with
  | nil =>
    cases signed <;> cases tokens <;> simp_all [readG05OrderedRows487]
  | cons a rest ih =>
    cases signed with
    | nil => simp [readG05OrderedRows487] at ran
    | cons bit bits =>
      cases tokens with
      | nil => simp [readG05OrderedRows487] at ran
      | cons token allowed =>
        cases here : readG05OneRow487 p check offset a bit token with
        | none => simp [readG05OrderedRows487,here] at ran
        | some first =>
          cases later : readG05OrderedRows487 p check (offset+1) rest bits allowed with
          | none => simp [readG05OrderedRows487,here,later,Option.bind] at ran
          | some tail =>
            have exact : first::tail = rows :=
              Option.some.inj (by simpa [readG05OrderedRows487,here,later,Option.bind] using ran)
            subst rows
            obtain ⟨len,steps⟩ := ih later
            refine ⟨by simp [len],?_⟩
            intro j row got
            cases j with
            | zero =>
              have same : first = row := Option.some.inj got
              subst row
              exact ⟨a,bit,token,rfl,rfl,rfl,by simpa using here⟩
            | succ k =>
              obtain ⟨c,s,t,h1,h2,h3,h4⟩ := steps k row got
              refine ⟨c,s,t,h1,h2,h3,?_⟩
              have shift : (offset+1)+k = offset+(k+1) := by omega
              rw [shift] at h4
              exact h4

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
