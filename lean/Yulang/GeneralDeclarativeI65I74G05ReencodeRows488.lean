import Yulang.GeneralDeclarativeI65I74G05EquivalentEncoding488

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485

def reencodeG05Rows488 {n : Nat} :
    List (G05CandidateRow487 n) → List (ComputedOriginalCandidate486 n) → List (G05CandidateRow487 n)
  | r::more,c::rest => {r with observed := c.keys} :: reencodeG05Rows488 more rest
  | _,_ => []

def g05RowMarkPairs488 {n : Nat} (rows : List (G05CandidateRow487 n)) :=
  rows.map fun r => (r.ordinal,r.mark)

theorem reencoded_g05_rows_keep_the_exact_ordered_marks488
    {n : Nat} {rs : List (G05CandidateRow487 n)} {compiled : List (ComputedOriginalCandidate486 n)}
    (len : rs.length = compiled.length) :
    g05RowMarkPairs488 (reencodeG05Rows488 rs compiled) = g05RowMarkPairs488 rs := by
  induction rs generalizing compiled with
  | nil => cases compiled <;> simp_all [reencodeG05Rows488,g05RowMarkPairs488]
  | cons r rest ih =>
    cases compiled with
    | nil => simp at len
    | cons c next =>
      have back := ih (Nat.succ.inj len)
      change (r.ordinal,r.mark)::g05RowMarkPairs488 (reencodeG05Rows488 rest next) =
        (r.ordinal,r.mark)::g05RowMarkPairs488 rest
      rw [back]

theorem same_ordered_marks_imply_same_prioritized_g05_scope488
    {n : Nat} {a b : List (G05CandidateRow487 n)}
    (marks : g05RowMarkPairs488 a = g05RowMarkPairs488 b) :
    G05PriorityOfRows487 a = G05PriorityOfRows487 b := by
  let hits := fun (pair : Nat × G05CandidateMark487) => match pair.2 with
    | .requiredCycle => some pair.1
    | .nonrecursive _ => none
  let safe := fun (pair : Nat × G05CandidateMark487) => match pair.2 with
    | .requiredCycle => none
    | .nonrecursive v => some (pair.1,v)
  let conclude (h : List Nat) (v : List (Nat × G05LocalVerdict487)) : G05Priority487 :=
    match h with | [] => .eligible v | first::rest => .recursive (first::rest)
  have view (l : List (G05CandidateRow487 n)) :
      G05PriorityOfRows487 l =
      conclude ((g05RowMarkPairs488 l).filterMap hits) ((g05RowMarkPairs488 l).filterMap safe) := by
    simp only [g05RowMarkPairs488,List.filterMap_map,Function.comp_def]
    rfl
  rw [view a,view b,marks]

theorem reencoding_the_report_with_canonical_path_lists_keeps_each_exact_row_identity488
    {n : Nat} {rs : List (G05CandidateRow487 n)} {compiled : List (ComputedOriginalCandidate486 n)}
    (len : rs.length = compiled.length) :
    (reencodeG05Rows488 rs compiled).length = rs.length ∧
    ∀ (i : Nat) (r : G05CandidateRow487 n) (c : ComputedOriginalCandidate486 n),
      rs[i]? = some r → compiled[i]? = some c →
      (reencodeG05Rows488 rs compiled)[i]? = some {r with observed := c.keys} := by
  induction rs generalizing compiled with
  | nil => cases compiled <;> simp_all [reencodeG05Rows488]
  | cons r rest ih =>
    cases compiled with
    | nil => simp at len
    | cons c next =>
      obtain ⟨count,atIndex⟩ := ih (Nat.succ.inj len)
      refine ⟨congrArg Nat.succ count,?_⟩
      intro i row candidate got found
      cases i with
      | zero =>
        have rSame : r = row := Option.some.inj got
        have cSame : c = candidate := Option.some.inj found
        subst row
        subst candidate
        rfl
      | succ k => exact atIndex k row candidate got found

theorem indexed_ordinal_mark_and_visit_membership_reify_report_equivalence488
    {n : Nat} {a b : List (G05CandidateRow487 n)} (len : a.length = b.length)
    (atSlot : ∀ (i : Nat) (r s : G05CandidateRow487 n), a[i]? = some r → b[i]? = some s →
      r.ordinal = s.ordinal ∧ r.mark = s.mark ∧ ∀ key, key ∈ r.observed ↔ key ∈ s.observed) :
    g05ReportRowsEquivalent488 a b = true := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [g05ReportRowsEquivalent488]
  | cons head later ih =>
    cases b with
    | nil => simp at len
    | cons front rest =>
      obtain ⟨authored,status,keys⟩ := atSlot 0 head front rfl rfl
      have same : g05ReportRowEquivalent488 head front = true := by
        unfold g05ReportRowEquivalent488
        exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
          ⟨decide_eq_true authored,decide_eq_true status⟩,
          (g05VisitMembershipEqual_is_exact488 _ _).mpr keys⟩
      have back := ih (Nat.succ.inj len) (fun j r s one two => atSlot (j+1) r s one two)
      simp [g05ReportRowsEquivalent488,same,back]

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
