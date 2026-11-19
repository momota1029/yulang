import Yulang.GeneralRebaseRoundProjection265

namespace Yulang.GeneralRebaseStutterRank266
open GeneralRebaseLiveProjection264 (SourceState project)
open GeneralSourceState (Output)

/-- A secondary natural measure is required only where the fixed projection
does not change. This requirement is not hidden in the finite state. -/
def Descends (owners : List Nat) (pool : List Output)
 (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (secondary : SourceState roles → Nat) : Prop :=
 ∀ before after, GeneralNominalVersionedMixedKernel234.Step registry root before after →
 project owners pool after = project owners pool before → secondary after < secondary before

theorem source_wf (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 (secondary : SourceState roles → Nat) (stutter : Descends owners pool registry root secondary) :
 WellFounded (fun after before => GeneralNominalVersionedMixedKernel234.Step registry root before after) := by
 let rank := fun state : SourceState roles => ((project owners pool state).remaining.length, secondary state)
 apply Subrelation.wf (r := InvImage (Prod.Lex Nat.lt Nat.lt) rank) _
   (InvImage.wf rank (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf)
 intro after before step
 change Prod.Lex Nat.lt Nat.lt (rank after) (rank before)
 rw [Prod.lex_def]
 by_cases same : project owners pool after = project owners pool before
 · exact Or.inr ⟨congrArg (fun t => t.remaining.length) same,stutter _ _ step same⟩
 · exact Or.inl (GeneralRebaseSourceProjection264.strict_decrease owners pool step same)

/-- The old 239 kernel cannot admit such a uniform secondary rank for any
fixed basis. This says nothing negative about a redesigned, novelty-gated Step. -/
theorem no_old239_rank (owners : List Nat) (pool : List Output) :
 ¬ ∃ secondary, Descends owners pool GeneralDictionaryVersionLoopSource237.registry
     GeneralDictionaryVersionLoopSource237.root secondary := by
 rintro ⟨secondary,stutter⟩
 exact GeneralDictionaryVersionLoopNontermination239.no_acc 0
   ((source_wf owners pool secondary stutter).apply (GeneralDictionaryVersionLoopIteration239.state 0))

end Yulang.GeneralRebaseStutterRank266
