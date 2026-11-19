import Yulang.GeneralRebasePathQuiescent266
import Yulang.GeneralDictionaryLooseIterationNontermination240
import Yulang.GeneralNominalPointErasure240

namespace Yulang.GeneralRebaseRecurrence266
open GeneralRebaseStep258
open GeneralRebaseCertifiedObserver266 (observe)
open GeneralRebaseCertifiedPath266 (Path edges)
open GeneralRebaseCertifiedPathCount266 (strict_count)
open GeneralRebaseLiveProjection264 (SourceState project)
open GeneralSourceState (Output)
variable {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}

def Quiet (owners : List Nat) (pool : List Output) (path : Path registry root first last) : Prop :=
 strict_count owners pool path = 0 ∧
 ∀ state, GeneralRebaseScheduler259.next (observe owners pool (edges path)) state = .ok none

theorem quiet_of_endpoints (owners : List Nat) (pool : List Output)
 (path : Path registry root first last) (same : project owners pool first = project owners pool last) :
 Quiet owners pool path :=
 ⟨GeneralRebasePathQuiescent266.count_zero owners pool path same,
  GeneralRebasePathQuiescent266.immediate owners pool path same⟩

theorem point_round_old
 (path : Relation.TransGen (fun after before =>
    GeneralNominalPointKernel240.Step registry root before after) last first) :
 Relation.TransGen (fun after before =>
    GeneralNominalVersionedMixedKernel234.Step registry root before after) last first := by
 induction path with
 | single step => exact .single (GeneralNominalPointErasure240.step_old step)
 | tail _ step ih => exact .tail ih (GeneralNominalPointErasure240.step_old step)

theorem suffix (owners : List Nat) (pool : List Output) (state : Nat → SourceState roles)
 (backward : ∀ n, Relation.TransGen (fun after before =>
    GeneralNominalVersionedMixedKernel234.Step registry root before after) (state (n+1)) (state n)) :
 ∃ N, ∀ n ≥ N,
 (Nonempty (Path registry root (state n) (state (n+1)))) ∧
 (∀ path : Path registry root (state n) (state (n+1)), Quiet owners pool path) := by
 obtain ⟨N,stable⟩ := GeneralRebaseRoundProjection265.eventual_rounds owners pool state backward
 refine ⟨N,fun n ge => ⟨GeneralRebasePathQuiescent266.of_round (backward n),fun path => ?_⟩⟩
 exact quiet_of_endpoints owners pool path
   ((stable n ge).trans (stable (n+1) (Nat.le_trans ge (Nat.le_succ n))).symm)

theorem version239 (owners : List Nat) (pool : List Output) :
 ∃ N, ∀ n ≥ N,
 ¬ Acc GeneralDictionaryVersionLoopNontermination239.reverseStep (GeneralDictionaryVersionLoopIteration239.state n) ∧
 Nonempty (Path GeneralDictionaryVersionLoopSource237.registry GeneralDictionaryVersionLoopSource237.root
   (GeneralDictionaryVersionLoopIteration239.state n) (GeneralDictionaryVersionLoopIteration239.state (n+1))) ∧
 (∀ path : Path GeneralDictionaryVersionLoopSource237.registry GeneralDictionaryVersionLoopSource237.root
   (GeneralDictionaryVersionLoopIteration239.state n) (GeneralDictionaryVersionLoopIteration239.state (n+1)),
   Quiet owners pool path) := by
 obtain ⟨N,h⟩ := suffix owners pool GeneralDictionaryVersionLoopIteration239.state
   GeneralDictionaryVersionLoopNontermination239.backward_round
 exact ⟨N,fun n ge => ⟨GeneralDictionaryVersionLoopNontermination239.no_acc n,h n ge⟩⟩

theorem version240 (owners : List Nat) (pool : List Output) :
 ∃ N, ∀ n ≥ N,
 ¬ Acc GeneralDictionaryLooseIterationNontermination240.reverseStep (GeneralDictionaryLooseIterationIteration240.state n) ∧
 Nonempty (Path GeneralDictionaryLooseLoopSource240.registry GeneralDictionaryLooseLoopSource240.root
   (GeneralDictionaryLooseIterationIteration240.state n) (GeneralDictionaryLooseIterationIteration240.state (n+1))) ∧
 (∀ path : Path GeneralDictionaryLooseLoopSource240.registry GeneralDictionaryLooseLoopSource240.root
   (GeneralDictionaryLooseIterationIteration240.state n) (GeneralDictionaryLooseIterationIteration240.state (n+1)),
   Quiet owners pool path) := by
 obtain ⟨N,h⟩ := suffix owners pool GeneralDictionaryLooseIterationIteration240.state
   (fun n => point_round_old (GeneralDictionaryLooseIterationNontermination240.backward_round n))
 exact ⟨N,fun n ge => ⟨GeneralDictionaryLooseIterationNontermination240.no_acc n,h n ge⟩⟩

end Yulang.GeneralRebaseRecurrence266
