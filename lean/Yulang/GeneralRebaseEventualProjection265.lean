import Yulang.GeneralRebaseProjectedBudget264

namespace Yulang.GeneralRebaseEventualProjection265
open GeneralRebaseLiveProjection264 (SourceState project)
open GeneralSourceState (Output)

/-- If adjacent values are equal or strictly descend in a natural measure, the
sequence is eventually constant as values, not just as measures. -/
theorem stabilizes {α : Type u} (state : Nat → α) (measure : α → Nat)
 (changeOrDecrease : ∀ n, state (n+1) = state n ∨ measure (state (n+1)) < measure (state n)) :
 ∃ N, ∀ n ≥ N, state n = state N := by
 classical
 let rank := fun n => measure (state n)
 have least (k : Nat) (existsBound : ∃ n, rank n ≤ k) :
     ∃ N, ∀ n, rank N ≤ rank n := by
   induction k with
   | zero =>
     obtain ⟨N,bound⟩ := existsBound
     exact ⟨N,fun n => by omega⟩
   | succ k ih =>
     by_cases smaller : ∃ n, rank n ≤ k
     · exact ih smaller
     · obtain ⟨N,bound⟩ := existsBound
       refine ⟨N,fun n => ?_⟩
       have excluded : ¬rank n ≤ k := fun hn => smaller ⟨n,hn⟩
       omega
 obtain ⟨N,minimum⟩ := least (rank 0) ⟨0,Nat.le_refl _⟩
 have suffix (d : Nat) : state (N+d) = state N := by
   induction d with
   | zero => rfl
   | succ d ih =>
     change state ((N+d)+1) = state N
     rcases changeOrDecrease (N+d) with same | decreasing
     · exact same.trans ih
     · have rankEqual : rank (N+d) = rank N := congrArg measure ih
       exact False.elim ((Nat.not_lt_of_ge (minimum ((N+d)+1))) (rankEqual ▸ decreasing))
 refine ⟨N,fun n ge => ?_⟩
 have indices : N + (n-N) = n := by omega
 exact indices ▸ suffix (n-N)

/-- A fixed finite projection of an infinite genuine source trace eventually
becomes exactly constant. The source states themselves need not stabilize. -/
theorem eventual_constant (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 (state : Nat → SourceState roles)
 (step : ∀ n, GeneralNominalVersionedMixedKernel234.Step registry root (state n) (state (n+1))) :
 ∃ N, ∀ n ≥ N, project owners pool (state n) = project owners pool (state N) := by
 apply stabilizes (fun n => project owners pool (state n)) (fun s => s.remaining.length)
 intro n
 by_cases same : project owners pool (state (n+1)) = project owners pool (state n)
 · exact Or.inl same
 · exact Or.inr (GeneralRebaseSourceProjection264.strict_decrease owners pool (step n) same)

end Yulang.GeneralRebaseEventualProjection265
