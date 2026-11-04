import Yulang.Horn

/-!
Small finite constraints exercise the reference algorithm, while the
quantified correctness results remain in `Yulang.Horn`. These are not
surface Yulang programs or a test of source elaboration.
-/

namespace Yulang.Horn.Examples

def bits (value : Valuation n) : List Bool := (List.finRange n).map value

/-- A positive seed flows through the entire inclusion chain. -/
def propagation : Problem 4 :=
  [.seed 0, .include 0 1, .include 1 2, .forbid [3]]

theorem propagation_result :
    (solve propagation).map bits = some [true, true, true, false] := by decide

/-- A cycle alone does not invent a true fact. -/
def unseededCycle : Problem 2 := [.include 0 1, .include 1 0]

theorem unseededCycle_result :
    (solve unseededCycle).map bits = some [false, false] := by decide

/-- Multi-premise Horn implications require all premises. -/
def conjunction : Problem 3 := [.seed 0, ⟨[0, 1], some 2⟩]

theorem conjunction_waits_for_both :
    (solve conjunction).map bits = some [true, false, false] := by decide

theorem conjunction_fires :
    (solve (.seed 1 :: conjunction)).map bits = some [true, true, true] := by decide

def contradiction : Problem 2 := [.seed 0, .include 0 1, .forbid [1]]

theorem contradiction_rejected : solve contradiction = none := by decide

/-- Rejection has the declarative meaning claimed by the solver. -/
theorem contradiction_has_no_model : ¬ ∃ value, Models contradiction value :=
  (solve_eq_none_iff contradiction).mp contradiction_rejected

theorem empty_problem_is_all_false :
    (solve ([] : Problem 3)).map bits = some [false, false, false] := by decide

theorem zero_facts_has_empty_model :
    (solve ([] : Problem 0)).map bits = some [] := by decide

/-- The empty conjunction is true, so forbidding it is inconsistent. -/
theorem empty_premises_forbidden :
    solve ([.forbid []] : Problem 0) = none := by decide

#print axioms Yulang.Horn.check_iff
#print axioms Yulang.Horn.mem_valuations
#print axioms Yulang.Horn.intersection_models
#print axioms Yulang.Horn.solve_principal
#print axioms Yulang.Horn.solve_eq_none_iff
#print axioms Yulang.Horn.solve_complete
#print axioms Yulang.Horn.solve_eq_some_iff
#print axioms propagation_result
#print axioms contradiction_has_no_model

end Yulang.Horn.Examples
