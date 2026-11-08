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

/-- `stream` contains one function field; each result contains one element
and another stream. The reference back to node 0 is behind the wrapper. -/
def stream : Plan 6 := fun node =>
  match node.val with
  | 0 => .nominal 1
  | 1 => .product [2]
  | 2 => .function 3 4
  | 3 => .keep
  | 4 => .product [5, 0]
  | _ => .leaf

theorem stream_checked : check stream = true := by decide

private theorem stream_root : stream 0 = .nominal 1 := rfl
private theorem stream_fields : stream 1 = .product [2] := rfl
private theorem stream_next : stream 2 = .function 3 4 := rfl
private theorem stream_argument : stream 3 = .keep := rfl
private theorem stream_result : stream 4 = .product [5, 0] := rfl
private theorem stream_element : stream 5 = .leaf := rfl

def streamValue (token : Nat) : Value 6 := .nominal (.product [.function token])
def streamWrapped (token : Nat) : Value 6 := .nominal (.product [.wrapper 2 (.function token)])

private def streamResult (token : Nat) : Result stream 0 :=
  ⟨streamWrapped token, 3,
    .nominal stream_root (.product stream_fields (.cons (.function stream_next) .nil))⟩

private theorem stream_evaluates (leaf : Leaf 6) (token : Nat) :
    evaluate stream stream_checked leaf 0 (streamValue token) = some (streamResult token) := by
  unfold streamValue
  rw [evaluate_nominal _ _ _ 0 1 stream_root]
  rw [evaluate_product _ _ _ 1 [2] stream_fields]
  simp only [evaluateParts]
  rw [evaluate_function _ _ _ 2 3 4 stream_next]
  rfl

/-- Even an always-failing leaf primitive cannot prevent wrapper creation:
the recursive payload and future result are not converted yet. -/
theorem stream_creation (leaf : Leaf 6) (token : Nat) :
    executeChecked stream leaf 0 (streamValue token) = some (streamWrapped token, 3) := by
  unfold executeChecked
  rw [dite_eq_left stream_checked]
  unfold execute
  rw [stream_evaluates]
  rfl

theorem stream_creation_budget : budget stream stream_checked 0 = 3 := by
  rw [CommonDeclaredCastCost.budget_eq]
  change 1 + budget stream stream_checked 1 = 3
  rw [CommonDeclaredCastCost.budget_eq]
  change 1 + (1 + budget stream stream_checked 2) = 3
  rw [CommonDeclaredCastCost.budget_eq]
  rfl

def streamBody : Body 6 := fun original _ =>
  match original with
  | .function token => some (.product [.atom token, streamValue (token + 1)])
  | _ => none

private theorem invoke_function (plan : Plan n) (accepted : check plan = true)
    (leaf : Leaf n) (body : Body n) (node argument result : Fin n)
    (shape : plan node = .function argument result) (original input : Value n) :
    invokeWrapper plan accepted leaf body node original input =
      if original.callable then do
        let before ← evaluate plan accepted leaf argument input
        let middle ← body original before.value
        let after ← evaluate plan accepted leaf result middle
        pure ⟨after.value, before.cost + 1 + after.cost,
          .call shape before.execution after.execution⟩
      else none := by
  unfold invokeWrapper
  split
  next actualArgument actualResult nodeEq =>
    have same := Node.function.inj (shape.symm.trans nodeEq)
    rcases same with ⟨rfl, rfl⟩
    rfl
  next absent => exact False.elim (absent argument result shape)

/-- A real call converts one returned element and wraps the next stream.
The next opaque function is retained, not called recursively. -/
theorem stream_one_call (token unit : Nat) :
    invoke stream stream_checked increment streamBody (.wrapper 2 (.function token)) (.atom unit) =
      some (.product [.atom (token + 1), streamWrapped (token + 1)], 7) := by
  dsimp only [invoke]
  rw [invoke_function _ _ _ _ 2 3 4 stream_next]
  simp only [Value.callable, ite_true]
  rw [evaluate_keep _ _ _ 3 stream_argument]
  dsimp only [streamBody]
  simp only [Bind.bind, Option.bind]
  rw [evaluate_product _ _ _ 4 [5, 0] stream_result]
  simp only [evaluateParts]
  rw [evaluate_leaf _ _ _ 5 stream_element]
  simp only [increment, Option.map_some, Bind.bind, Option.bind]
  rw [stream_evaluates]
  rfl

theorem stream_call_budget : callBudget stream stream_checked 3 4 = 7 := by
  have argument : budget stream stream_checked 3 = 1 := by
    rw [CommonDeclaredCastCost.budget_eq]
    rfl
  have element : budget stream stream_checked 5 = 1 := by
    rw [CommonDeclaredCastCost.budget_eq]
    rfl
  have result : budget stream stream_checked 4 = 5 := by
    rw [CommonDeclaredCastCost.budget_eq]
    change 1 + (budget stream stream_checked 5 + (budget stream stream_checked 0 + 0)) = 5
    rw [element, stream_creation_budget]
  simp [callBudget, argument, result]

end Yulang.CommonDeclaredCastEvaluationExamples
