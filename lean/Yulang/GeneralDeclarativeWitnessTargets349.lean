import Yulang.GeneralDeclarativeWitnessProblem349

namespace Yulang.GeneralDeclarativeWitnessTargets349
open GeneralSourceState (Output)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessProblem349 (Problem)

private def outEq (a b : Output) : Decidable (a = b) :=
  decidable_of_iff (a.name = b.name ∧ a.target = b.target) (by
    constructor
    · cases a; cases b
      simp
    · intro eq; cases eq; exact ⟨rfl,rfl⟩)

local instance : DecidableEq Output := outEq

/-- Equality of the literal ordered list of public requests, not set
equality and not just equality of association names. -/
def same_requests (p : Problem) (reported : List Output) : Bool :=
  decide (reported = p.demand.outputs)

theorem exact_targets (p : Problem) (reported : List Output) :
    same_requests p reported = true ↔ reported = p.demand.outputs := by
  unfold same_requests
  exact decide_eq_true_iff

theorem exact_ordinal {p : Problem} {reported : List Output}
    (received : same_requests p reported = true) (ix : Nat) :
    reported[ix]? = p.demand.outputs[ix]? := by
  rw [(exact_targets _ _).mp received]

end Yulang.GeneralDeclarativeWitnessTargets349
