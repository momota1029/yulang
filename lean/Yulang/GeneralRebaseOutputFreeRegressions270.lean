import Yulang.GeneralRebaseNoOutputs270
import Yulang.GeneralRebaseBehaviorRegression269

namespace Yulang.GeneralRebaseOutputFreeRegressions270
open GeneralRebaseNoOutputs270 (OutputFree terminalCode exact_code)
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseBehavior269 (code)
open GeneralRebaseWeakProgress268 (Weak)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralSourceState (Output)

namespace Version239
open GeneralDictionaryVersionLoopSource237 (registry context root initial)
open GeneralDictionaryVersionLoopIteration239 (state round)

theorem registry_free : OutputFree registry := by
 intro declaration listed
 cases List.mem_singleton.mp listed
 intro clause absent
 cases absent

theorem finite_prefix (n : Nat) : B4Target.Steps (Step registry root) initial (state n) := by
 induction n with
 | zero => exact .refl
 | succ i ih => exact GeneralRebaseWeakTerminal268.append ih (round i)

theorem all_reachable_code (owners : List Nat) (pool : List Output) (n : Nat) :
 code registry root owners pool (state n) = terminalCode (Basis owners pool) :=
 exact_code registry context root registry_free rfl (finite_prefix n) owners pool

theorem visible_stop (owners : List Nat) (pool : List Output) (n fuel : Nat) :
 FiniteBehaviorDriver269.drive fuel (code registry root owners pool (state n)) = (0,terminalCode (Basis owners pool)) ∧
 ¬ Acc GeneralDictionaryVersionLoopNontermination239.reverseStep (state n) := by
 rw [all_reachable_code owners pool n]
 exact ⟨GeneralRebaseNoOutputs270.executable_stop _ fuel,GeneralDictionaryVersionLoopNontermination239.no_acc n⟩

end Version239

namespace Version240
open GeneralDictionaryLooseLoopSource240 (registry context root initial)
open GeneralDictionaryLooseIterationIteration240 (state round)

theorem registry_free : OutputFree registry := by
 intro declaration listed
 cases List.mem_singleton.mp listed
 intro clause absent
 cases absent

theorem finite_prefix (n : Nat) : B4Target.Steps (Step registry root) initial (state n) := by
 induction n with
 | zero => exact .refl
 | succ i ih => exact GeneralRebaseWeakTerminal268.append ih (GeneralNominalPointErasure240.steps_old (round i))

theorem all_reachable_code (owners : List Nat) (pool : List Output) (n : Nat) :
 code registry root owners pool (state n) = terminalCode (Basis owners pool) :=
 exact_code registry context root registry_free rfl (finite_prefix n) owners pool

theorem visible_stop (owners : List Nat) (pool : List Output) (n fuel : Nat) :
 FiniteBehaviorDriver269.drive fuel (code registry root owners pool (state n)) = (0,terminalCode (Basis owners pool)) ∧
 ¬ Acc GeneralDictionaryLooseIterationNontermination240.reverseStep (state n) := by
 rw [all_reachable_code owners pool n]
 exact ⟨GeneralRebaseNoOutputs270.executable_stop _ fuel,GeneralDictionaryLooseIterationNontermination240.no_acc n⟩

end Version240
end Yulang.GeneralRebaseOutputFreeRegressions270
