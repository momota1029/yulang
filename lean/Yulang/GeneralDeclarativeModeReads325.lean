import Yulang.GeneralDeclarativeForwardHead325
import Yulang.GeneralDeclarativeTraceNames321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeModeReads325
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeTraceTransfer325 (ordinary)
open GeneralDeclarativeTrace321 (Trace Links trace_model)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeAliasMeaning321 (alias_sound)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralNominalExpressionIntervals237 (reads value_mono)
open CommonNominalFullCarrier (Equivalent subtype_trans)
open GeneralDeclarationPatterns (normalize)

def SameAt (s : State) (cap : Nat → Capture) (e : Expr) : Prop :=
  ∀ n ∈ reads e, Alias s (cap n).lower (cap n).center ∧ Alias s (cap n).upper (cap n).center

theorem invisible_modes {s : State} (point : SameAt s cap code) (m) (valid : Models s m) :
    Equivalent (value (variables cap m) .lower code) (value (variables cap m) .actual code) ∧
    Equivalent (value (variables cap m) .upper code) (value (variables cap m) .actual code) := by
  constructor <;> constructor <;> apply value_mono
  · intro n used
    exact (alias_sound (point n used).1 m valid).1
  · intro n used
    exact (alias_sound (point n used).1 m valid).2
  · intro n used
    exact (alias_sound (point n used).2 m valid).1
  · intro n used
    exact (alias_sound (point n used).2 m valid).2

/-- For mode-sensitive binds ordinary aliases can discharge the two
reverse inequalities. No identity of numerical names and no actual
constructor equation at the center are required. Variables underneath
invariant constructors do not count as mode-sensitive reads. -/
theorem compiled_from_ends {s : State} {support : Supported s complete}
    (bounds : Bounds s arg)
    (written : translate c i (normalize p) = some code)
    (lower : Trace (restriction support) .lower arg.lower code rawLo) (loLink : Links s cap rawLo)
    (upper : Trace s .upper arg.upper code rawHi) (hiLink : Links s cap rawHi)
    (point : SameAt s cap code) : Result s (fact c i cap arg p) := by
  refine ⟨[⟨arg.center,logical cap .actual code⟩],by simp [fact,written],?_⟩
  intro row member m valid
  cases List.mem_singleton.mp member
  have span := bounds_sound bounds m valid
  have agreement := invisible_modes point m valid
  have lo := eqv_trans (trace_model m valid cap (ordinary support lower) loLink) agreement.1
  have hi := eqv_trans (trace_model m valid cap upper hiLink) agreement.2
  rw [Holds,logical_value]
  exact ⟨subtype_trans span.2 hi.1,subtype_trans lo.2 span.1⟩

end Yulang.GeneralDeclarativeModeReads325
