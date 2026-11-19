import Yulang.GeneralRebaseChangedCode269
import Yulang.GeneralRebaseRecurrence266

namespace Yulang.GeneralRebaseBehaviorRegression269
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralRebaseBehavior269 (code)
open GeneralRebaseChangedCode269 (rank old_or_drop eventual_rounds)
open GeneralSourceState (Output)

theorem path_or_drop (path : B4Target.Steps (Step registry root) first last)
 (owners : List Nat) (pool : List Output) :
 code registry root owners pool last = code registry root owners pool first ∨
 rank owners pool (code registry root owners pool last) < rank owners pool (code registry root owners pool first) := by
 induction path with
 | refl => exact Or.inl rfl
 | tail _ move smaller =>
   rcases old_or_drop registry root owners pool _ _ move with same | drop
   · rwa [same]
   · rcases smaller with same | prev
     · exact Or.inr (same ▸ drop)
     · exact Or.inr (Nat.lt_trans drop prev)

theorem constant_between (beforePath : B4Target.Steps (Step registry root) first middle)
 (suffix : B4Target.Steps (Step registry root) middle last)
 (owners : List Nat) (pool : List Output)
 (same : code registry root owners pool last = code registry root owners pool first) :
 code registry root owners pool middle = code registry root owners pool first := by
 rcases path_or_drop beforePath owners pool with fixed | drop
 · exact fixed
 · rcases path_or_drop suffix owners pool with equal | more
   · rw [←equal,same] at drop
     exact False.elim (Nat.lt_irrefl _ drop)
   · rw [same] at more
     exact False.elim (Nat.lt_asymm more drop)

theorem version239 (owners : List Nat) (pool : List Output) :
 ∃ N, ∀ n ≥ N,
 code GeneralDictionaryVersionLoopSource237.registry GeneralDictionaryVersionLoopSource237.root owners pool
   (GeneralDictionaryVersionLoopIteration239.state n) =
 code GeneralDictionaryVersionLoopSource237.registry GeneralDictionaryVersionLoopSource237.root owners pool
   (GeneralDictionaryVersionLoopIteration239.state N) ∧
 ¬ Acc GeneralDictionaryVersionLoopNontermination239.reverseStep (GeneralDictionaryVersionLoopIteration239.state n) := by
 obtain ⟨N,codes⟩ := eventual_rounds _ _ owners pool _ GeneralDictionaryVersionLoopNontermination239.backward_round
 exact ⟨N,fun n after => ⟨codes n after,GeneralDictionaryVersionLoopNontermination239.no_acc n⟩⟩

/-- PointKernel240 rounds are erased to the mixed kernel before classifying.
This is not a characterization of all same-source PointKernel240 weak edges. -/
theorem version240_mixed_observation (owners : List Nat) (pool : List Output) :
 ∃ N, ∀ n ≥ N,
 code GeneralDictionaryLooseLoopSource240.registry GeneralDictionaryLooseLoopSource240.root owners pool
   (GeneralDictionaryLooseIterationIteration240.state n) =
 code GeneralDictionaryLooseLoopSource240.registry GeneralDictionaryLooseLoopSource240.root owners pool
   (GeneralDictionaryLooseIterationIteration240.state N) ∧
 ¬ Acc GeneralDictionaryLooseIterationNontermination240.reverseStep (GeneralDictionaryLooseIterationIteration240.state n) := by
 obtain ⟨N,codes⟩ := eventual_rounds _ _ owners pool _ (fun n =>
   GeneralRebaseRecurrence266.point_round_old (GeneralDictionaryLooseIterationNontermination240.backward_round n))
 exact ⟨N,fun n after => ⟨codes n after,GeneralDictionaryLooseIterationNontermination240.no_acc n⟩⟩

end Yulang.GeneralRebaseBehaviorRegression269
