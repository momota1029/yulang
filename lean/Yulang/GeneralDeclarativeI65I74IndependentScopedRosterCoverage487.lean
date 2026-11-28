import Yulang.GeneralDeclarativeI65I74IndependentScopedArgumentCoverage487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open GeneralDeclarations (Declaration)

private theorem ordered_mapM_some_at_each_index487 {α β : Type} {f : α → Option β}
    {xs : List α} {ys : List β} (ran : xs.mapM (m := Option) f = some ys) {i : Nat} {x : α}
    (input : xs[i]? = some x) : ∃ y, ys[i]? = some y ∧ f x = some y := by
  induction xs generalizing ys i with
  | nil => simp at input
  | cons top tail ih =>
    cases front : f top with
    | none => simp [List.mapM_cons,front] at ran
    | some head =>
      cases rest : tail.mapM (m := Option) f with
      | none => simp [List.mapM_cons,front,rest] at ran
      | some more =>
        have xs : head::more = ys := Option.some.inj (by simpa [List.mapM_cons,front,rest] using ran)
        subst ys
        cases i with
        | zero =>
          have same : top = x := Option.some.inj input
          exact ⟨head,rfl,same ▸ front⟩
        | succ j =>
          obtain ⟨y,got,found⟩ := ih rest (show tail[j]? = some x from input)
          exact ⟨y,got,found⟩

theorem successful_scoped_candidate_retains_its_original_and_visible_ordinals487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {roots : List (Fin n)} {permit : Nat → CandidateVisitKey485 n → Bool}
    {i : Nat} {row : ComputedOriginalCandidate486 n}
    (ran : compileScopedCandidate487 p gd pos rel palette roots permit i = some row) :
    ∃ d, OriginalRosterCell485 p i (row.authoredOrdinal,d) ∧
      row.packet.visibleOrdinal = i ∧
      compileScopedArguments487 p gd pos rel palette i (permit row.authoredOrdinal) 0 roots =
        some (row.keys,row.packet.paths) := by
  unfold compileScopedCandidate487 at ran
  cases lookup : rosterCell485 p i with
  | none => simp [lookup] at ran
  | some pair =>
    obtain ⟨ordinal,d⟩ := pair
    simp only [lookup,bind,Option.bind] at ran
    split at ran
    · cases args : compileScopedArguments487 p gd pos rel palette i (permit ordinal) 0 roots with
      | none => simp [args] at ran
      | some packet =>
        obtain ⟨keys,wires⟩ := packet
        have stored : (⟨ordinal,keys,⟨i,wires⟩⟩ : ComputedOriginalCandidate486 n) = row :=
          Option.some.inj (by simpa [args] using ran)
        subst row
        exact ⟨d,(roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mp lookup,rfl,args⟩
    · cases ran

theorem successful_scoped_roster_reads_every_actual_visible_slot_and_its_exact_independent_visits487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {roots : List (Fin n)} {permit : Nat → CandidateVisitKey485 n → Bool}
    {rows : List (ComputedOriginalCandidate486 n)}
    (ran : compileScopedRoster487 p gd pos rel palette roots permit = some rows)
    (i : Fin (visible485 p).length)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key) :
    ∃ row d, rows[i.val]? = some row ∧ OriginalRosterCell485 p i.val (row.authoredOrdinal,d) ∧
      row.packet.visibleOrdinal = i.val ∧
      ∀ key, key ∈ row.keys ↔ ∃ root argument, (root,argument) ∈ roots.zipIdx ∧
        ∃ head : OriginalArgumentStart486 p gd pos i.val argument root,
          IndependentScopedVisit487 rel argument head.site (Allowed row.authoredOrdinal) key := by
  unfold compileScopedRoster487 at ran
  obtain ⟨row,stored,candidate⟩ := ordered_mapM_some_at_each_index487 ran (List.getElem?_range i.isLt)
  obtain ⟨d,scope,visible,trace⟩ := successful_scoped_candidate_retains_its_original_and_visible_ordinals487 candidate
  exact ⟨row,d,stored,scope,visible,fun key =>
    generated_ordered_arguments_cover_every_and_only_independent_scoped_original_argument487
      trace (Allowed row.authoredOrdinal) (lawful row.authoredOrdinal) key⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
