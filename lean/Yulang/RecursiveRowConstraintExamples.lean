import Yulang.RecursiveRowConstraints

/-!
# Fixed upper constraints on original recursive rows

The checks include an arbitrary upper expression over a genuinely infinite
least row, a new operation key introduced only by that expression, and an
active residual that remains unsupported rather than becoming a rejection.
An open-row example separates existence of a model from validity in all models.
-/

namespace Yulang.RecursiveRowConstraints.Examples

open RowInference (RowExpr)
open RecursiveRows (Problem Models algebra)
open SemilinearWeights (Weight)
open SemilinearRowAlgebra (Row decode)

def scalar (value : Int) : Weight 1 := fun _ => value

def even : Problem 1 Nat Nat :=
  [⟨7, .head 0⟩,
   ⟨7, .protect 0 Directed.allowNone (.protect 0 Directed.allowNone (.var 7))⟩]

/-- The residual acts after protection, and the other branch introduces a key
that occurs in no lower constraint. Both signed transformations matter. -/
def expression : RowExpr Nat (Fin 1) Nat :=
  .union
    (.residual [0] (.protect 0 Directed.allowNone (.var 7)))
    (.release 0 Directed.allowNone (.head 1))

def allowed : Row 1 Nat :=
  [(0, [⟨scalar 1, [scalar 2]⟩]), (1, [⟨scalar (-1), []⟩])]

def limits : List (Upper 1 Nat Nat) := [⟨expression, allowed⟩]

theorem no_upper_requirements_always_succeed (problem : Problem 1 Nat Nat) :
    check problem [] = some true := rfl

set_option maxRecDepth 100000 in
theorem arbitrary_upper_expression_accepts_infinite_solution :
    check even limits = some true := by decide

set_option maxRecDepth 100000 in
theorem upper_expression_cannot_hide_its_new_operation :
    check even [⟨expression, [(0, [⟨scalar 1, [scalar 2]⟩])]⟩] = some false := by decide

set_option maxRecDepth 100000 in
theorem active_query_guard_stays_unsupported :
    check even [⟨.residual [0] (.var 7), []⟩] = none := by decide

theorem accepted_problem_has_an_original_model :
    ∃ rows, Models even rows ∧ ∀ limit ∈ limits, ∀ occurrence,
      limit.row.eval (algebra 1 Nat) rows occurrence → decode limit.allowed occurrence :=
  (check_exact even limits true arbitrary_upper_expression_accepts_infinite_solution).mp rfl

theorem rejected_upper_has_no_original_model :
    ¬ ∃ rows, Models even rows ∧
      ∀ limit ∈ ([⟨expression, [(0, [⟨scalar 1, [scalar 2]⟩])]⟩] : List (Upper 1 Nat Nat)),
        ∀ occurrence,
        limit.row.eval (algebra 1 Nat) rows occurrence → decode limit.allowed occurrence :=
  (check_rejects even _ false upper_expression_cannot_hide_its_new_operation).mp rfl

def openLimits : List (Upper 1 Nat Nat) := [⟨.var 7, []⟩]

set_option maxRecDepth 100000 in
theorem empty_least_open_row_can_satisfy_empty_upper :
    check ([] : Problem 1 Nat Nat) openLimits = some true := by decide

/-- Acceptance is existential. A later or otherwise larger assignment need
not satisfy the earlier empty upper requirement. -/
theorem another_model_can_violate_the_accepted_upper :
    ∃ rows, Models ([] : Problem 1 Nat Nat) rows ∧
      ¬ (∀ limit ∈ openLimits, ∀ occurrence,
        limit.row.eval (algebra 1 Nat) rows occurrence → decode limit.allowed occurrence) := by
  refine ⟨fun _ _ => True, ?_, ?_⟩
  · simp [Models]
  · intro satisfied
    have impossible := satisfied ⟨.var 7, []⟩ (by simp [openLimits]) (Directed.raw 0) True.intro
    exact SemilinearRowAlgebra.meaning_empty _ _ impossible

end Yulang.RecursiveRowConstraints.Examples
