import Yulang.SolvedRecursiveRows
import Yulang.AutomaticRowSummaryExamples

/-!
# Whole-row regression checks on the original constraint syntax

These examples exercise operation-key collection, missing slots, duplicate
heads, genuinely infinite solutions, and unsupported active guards. They invoke
the executable original-AST adapter, not a preconstructed semilinear summary.
-/

namespace Yulang.SolvedRecursiveRows.Examples

def joined : RecursiveRows.Problem 1 Nat Nat :=
  [⟨7, .union (.head 0) (.head 1)⟩]

def separate : RecursiveRows.Problem 1 Nat Nat :=
  [⟨7, .head 1⟩, ⟨7, .head 0⟩, ⟨7, .head 1⟩]

def single : RecursiveRows.Problem 1 Nat Nat := [⟨7, .head 0⟩]

def unguardedOdd : RecursiveRows.Problem 1 Nat Nat :=
  [⟨7, .protect 0 Directed.allowNone (.head 0)⟩,
   ⟨7, .protect 0 Directed.allowNone (.protect 0 Directed.allowNone (.var 7))⟩]

theorem empty_problem_has_empty_summary :
    summarize ([] : RecursiveRows.Problem 1 Nat Nat) 9001 = some [] := by decide

theorem seedless_guarded_recursion_has_empty_summary :
    summarize ([⟨7, .residual [0] (.protect 0 Directed.allowNone (.var 7))⟩] :
      RecursiveRows.Problem 1 Nat Nat) 7 = some [] := by decide

set_option maxRecDepth 100000 in
theorem failed_head_guard_is_executed :
    queryEqual ([⟨7, .residual [0] (.head 0)⟩] :
      RecursiveRows.Problem 1 Nat Nat) [] 7 7 = some true := by decide

set_option maxRecDepth 100000 in
theorem repeated_reordered_heads_have_the_same_row :
    queryEqual joined separate 7 7 = some true := by decide

set_option maxRecDepth 100000 in
theorem every_operation_key_is_checked :
    querySubset joined single 7 7 = some false := by decide

set_option maxRecDepth 100000 in
theorem extra_operation_key_is_allowed_on_the_right :
    querySubset single joined 7 7 = some true := by decide

set_option maxRecDepth 100000 in
theorem missing_slot_has_empty_least_row :
    queryEqual joined [] 9001 9001 = some true := by decide

set_option maxRecDepth 100000 in
theorem infinite_odd_rows_equal_after_exact_guard_check :
    queryEqual AutomaticRowSummaries.Examples.odd unguardedOdd 7 7 = some true := by decide

set_option maxRecDepth 100000 in
theorem active_guard_does_not_become_a_negative_answer :
    querySubset AutomaticRowSummaries.Examples.blocked [] 7 7 = none := by decide

theorem reordered_original_least_solutions_equal :
    RecursiveRows.Derives joined 7 = RecursiveRows.Derives separate 7 :=
  (queryEqual_exact joined separate 7 7 true repeated_reordered_heads_have_the_same_row).mp rfl

theorem missing_operation_has_an_actual_counterexample :
    ∃ occurrence, RecursiveRows.Derives joined 7 occurrence ∧
      ¬ RecursiveRows.Derives single 7 occurrence :=
  (querySubset_rejects joined single 7 7 false every_operation_key_is_checked).mp rfl

end Yulang.SolvedRecursiveRows.Examples
