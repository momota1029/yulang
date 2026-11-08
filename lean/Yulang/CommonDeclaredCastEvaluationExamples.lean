import Yulang.CommonDeclaredCastEvaluation

/-!
# Concrete operational witnesses for declaration-motivated cast plans

These examples execute the real finite-value evaluator. They demonstrate
that its cost theorems are inhabited, including delayed recursive wrappers
and unchanged concrete recursive branches. The plans are written explicitly;
these are not a source-declaration-to-plan correctness theorem.
-/

namespace Yulang.CommonDeclaredCastEvaluationExamples

open CommonDeclaredCastCostGraph
open CommonDeclaredCastCost (budget callBudget)
open CommonDeclaredCastEvaluation

def increment : Leaf n := fun _ value =>
  match value with
  | .atom token => some (.atom (token + 1))
  | _ => none

/-- Two nested one-field nominal boxes. -/
def box : Plan 5 := fun node =>
  match node.val with
  | 0 => .nominal 1
  | 1 => .product [2]
  | 2 => .nominal 3
  | 3 => .product [4]
  | _ => .leaf

theorem box_checked : check box = true := by decide

def boxValue (token : Nat) : Value 5 :=
  .nominal (.product [.nominal (.product [.atom token])])

theorem box_executes (token : Nat) :
    executeChecked box increment 0 (boxValue token) = some (boxValue (token + 1), 5) := by
  unfold executeChecked
  rw [dite_eq_left box_checked]
  unfold execute boxValue
  rw [evaluate_nominal _ _ _ 0 1 rfl]
  rw [evaluate_product _ _ _ 1 [2] rfl]
  simp only [evaluateParts]
  rw [evaluate_nominal _ _ _ 2 3 rfl]
  rw [evaluate_product _ _ _ 3 [4] rfl]
  simp only [evaluateParts]
  rw [evaluate_leaf _ _ _ 4 rfl]
  rfl

theorem box_budget : budget box box_checked 0 = 5 := by
  rw [CommonDeclaredCastCost.budget_eq]
  change 1 + budget box box_checked 1 = 5
  rw [CommonDeclaredCastCost.budget_eq]
  change 1 + (1 + budget box box_checked 2) = 5
  rw [CommonDeclaredCastCost.budget_eq]
  change 1 + (1 + (1 + budget box box_checked 3)) = 5
  rw [CommonDeclaredCastCost.budget_eq]
  change 1 + (1 + (1 + (1 + budget box box_checked 4))) = 5
  rw [CommonDeclaredCastCost.budget_eq]
  rfl

end Yulang.CommonDeclaredCastEvaluationExamples
