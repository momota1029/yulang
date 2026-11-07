import Yulang.CommonPatternCoreBoundedSolved

/-! A fixed positional Core term cannot use the named callback invariance
contract. This is an interface obstruction, not an obstruction to full B2:
canonical matching or index transport can supply the intended integration. -/

namespace Yulang.CommonPatternIndexedDefaultBoundary

open Core
open CaseValues (Bindings)
open EvaluationTrace (Logged)
open CommonPatternBindingAlignment (LookupEq)

def positional (actual : Bindings Empty) (code : Required.Term) : Logged Empty Empty CommonData.Value :=
  Logged.ofResult (.ok (match code with
    | .var index => ((actual[index]?).map Prod.snd).getD (.literal .unit)
    | _ => .literal .unit))

def first : Bindings Empty := [(0, .literal (.int 10)), (1, .literal (.int 20))]
def last : Bindings Empty := [(1, .literal (.int 20)), (0, .literal (.int 10))]

theorem same_names : LookupEq first last := by
  intro name
  by_cases zero : name = 0
  · subst name; rfl
  · by_cases one : name = 1
    · subst name; rfl
    · simp [first, last, CommonPatternBindingAlignment.lookup, zero, one]

theorem different_index_zero : positional first (.var 0) ≠ positional last (.var 0) := by
  intro equal
  have results := congrArg Logged.result equal
  cases results

/-- Even a two-entry environment with identical named lookup suffices. The
fixed term .var 0 must be reindexed when its positional environment changes. -/
theorem positional_not_name_invariant : ¬ CommonPatternAlignedMatcher.DefaultInvariant positional := by
  intro invariant
  exact different_index_zero (invariant first last same_names (.var 0))

end Yulang.CommonPatternIndexedDefaultBoundary
