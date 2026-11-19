import Yulang.GeneralRebaseEventualProjection265
import Yulang.GeneralDictionaryVersionLoopNontermination239

namespace Yulang.GeneralRebaseRoundProjection265
open GeneralRebaseLiveProjection264 (SourceState project)
open GeneralSourceState (Output)

theorem step_or_decrease (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {first last : SourceState roles}
 (step : GeneralNominalVersionedMixedKernel234.Step registry root first last) :
 project owners pool last = project owners pool first ∨
 (project owners pool last).remaining.length < (project owners pool first).remaining.length := by
 by_cases same : project owners pool last = project owners pool first
 · exact Or.inl same
 · exact Or.inr (GeneralRebaseSourceProjection264.strict_decrease owners pool step same)

/-- A source round can stutter in the projection, or it strictly decreases the
remaining-length measure. The result also applies to non-unit rounds. -/
theorem round_or_decrease (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {first last : SourceState roles}
 (path : Relation.TransGen (fun after before =>
   GeneralNominalVersionedMixedKernel234.Step registry root before after) last first) :
 project owners pool last = project owners pool first ∨
 (project owners pool last).remaining.length < (project owners pool first).remaining.length := by
 induction path with
 | single step => exact step_or_decrease owners pool step
 | tail _ step ih =>
   rcases step_or_decrease owners pool step with same | drop
   · simpa only [←same] using ih
   · rcases ih with equal | decrease
     · exact Or.inr (equal.symm ▸ drop)
     · exact Or.inr (Nat.lt_trans decrease drop)

theorem eventual_rounds (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 (state : Nat → SourceState roles)
 (path : ∀ n, Relation.TransGen (fun after before =>
   GeneralNominalVersionedMixedKernel234.Step registry root before after) (state (n+1)) (state n)) :
 ∃ N, ∀ n ≥ N, project owners pool (state n) = project owners pool (state N) :=
 GeneralRebaseEventualProjection265.stabilizes (fun n => project owners pool (state n))
   (fun s => s.remaining.length) (fun n => round_or_decrease owners pool (path n))

/-- The real 239 rounds give continuing source transitions, yet every fixed
finite projection eventually stays constant. -/
theorem version239 (owners : List Nat) (pool : List Output) :
 ∃ N, (∀ n ≥ N, project owners pool (GeneralDictionaryVersionLoopIteration239.state n) =
   project owners pool (GeneralDictionaryVersionLoopIteration239.state N)) ∧
   ¬ Acc GeneralDictionaryVersionLoopNontermination239.reverseStep
       (GeneralDictionaryVersionLoopIteration239.state N) := by
 obtain ⟨N,stable⟩ := eventual_rounds owners pool _ GeneralDictionaryVersionLoopNontermination239.backward_round
 exact ⟨N,stable,GeneralDictionaryVersionLoopNontermination239.no_acc N⟩

end Yulang.GeneralRebaseRoundProjection265
