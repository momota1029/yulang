import Yulang.ValueBoundSolvers

/-!
# Executed unknown-type inference regressions

These calls pass only a finite constraint problem, never a guessed assignment.
The negative cases additionally use the solver theorem to rule out every
possible assignment. Latent negative balances remain visible to the checker.
-/

namespace Yulang.ValueBoundSolvers.Examples

open StructuralBase ValueBounds

abbrev Row := Directed.Row 1 Nat
abbrev TypeCode := Ty Row

def mixed : TypeCode := .union (.base .int) (.base .str)

private theorem signed_solved (problem : Problem m Row)
    (checked : accepts StructuralDecisions.checkSigned problem (least problem) = true) :
    solveSigned problem = some (least problem) := by
  simp only [solveSigned, solve, checked, ↓reduceIte]

private theorem signed_rejected (problem : Problem m Row)
    (checked : accepts StructuralDecisions.checkSigned problem (least problem) = false) :
    solveSigned problem = none := by
  simp only [solveSigned, solve, checked, Bool.false_eq_true, ↓reduceIte]

/-- Both seeds enter a strongly connected component and then flow to its exit. -/
def cycle : Problem 3 Row :=
  [.lower (.base .int) 0, .lower (.base .str) 1,
   .flow 0 1, .flow 1 0, .flow 1 2, .upper 2 mixed]

theorem cyclic_unknowns_are_solved : solveSigned cycle = some (least cycle) := by
  exact signed_solved cycle (by decide +kernel)

theorem cycle_exit_is_the_union :
    least cycle 2 = .union (.base .int) (.union (.base .str) .bottom) := by
  rfl

theorem cycle_exit_has_exact_meaning :
    SignedStructural.Subtype (least cycle 2) mixed ∧
      SignedStructural.Subtype mixed (least cycle 2) := by
  constructor <;> apply (StructuralDecisions.checkSigned_exact _ _).mp <;> decide +kernel

def impossibleCycle : Problem 3 Row := cycle ++ [.upper 2 (.base .int)]

theorem conflicting_upper_is_rejected : solveSigned impossibleCycle = none := by
  exact signed_rejected impossibleCycle (by decide +kernel)

theorem conflicting_upper_has_no_assignment :
    ¬ ∃ value, Models SignedStructural.RowLe impossibleCycle value :=
  (solveSigned_none_iff impossibleCycle).mp conflicting_upper_is_rejected

/-- A lower-bound-free SCC has the mathematical least solution bottom. This
does not authorize defaulting a weak source variable at EOF to bottom. -/
def unseeded : Problem 2 Row := [.flow 0 1, .flow 1 0]

theorem unseeded_cycle_does_not_create_a_type :
    solveSigned unseeded = some (fun _ => .bottom) := by
  exact signed_solved unseeded (by decide +kernel)

def recordBounds : Problem 1 Row :=
  [.lower (.record 0 (.base .int) (.record 1 (.base .str) .emptyRecord)) 0,
   .upper 0 (.record 0 (.base .int) .emptyRecord)]

theorem inferred_record_obeys_width : solveSigned recordBounds = some (least recordBounds) := by
  exact signed_solved recordBounds (by decide +kernel)

def hiddenDuplicate : Problem 1 Row :=
  [.lower (.record 0 (.base .int) (.record 0 (.base .str) .emptyRecord)) 0,
   .upper 0 (.record 0 (.base .str) .emptyRecord)]

theorem later_duplicate_cannot_repair_a_bound : solveSigned hiddenDuplicate = none := by
  exact signed_rejected hiddenDuplicate (by decide +kernel)

def functionBounds : Problem 1 Row :=
  [.lower (.arrow mixed [] (.base .int) []) 0,
   .upper 0 (.arrow (.base .int) [] mixed [])]

theorem inferred_function_respects_variance :
    solveSigned functionBounds = some (least functionBounds) := by
  exact signed_solved functionBounds (by decide +kernel)

def debt : Row := [⟨7, fun _ => -1⟩]

def debtBounds : Problem 1 Row :=
  [.lower (.arrow (.base .unit) [] (.base .int) debt) 0,
   .upper 0 (.arrow (.base .unit) [] (.base .int) [])]

theorem unknown_function_cannot_hide_negative_effects : solveSigned debtBounds = none := by
  exact signed_rejected debtBounds (by decide +kernel)

theorem hidden_negative_effects_have_no_assignment :
    ¬ ∃ value, Models SignedStructural.RowLe debtBounds value :=
  (solveSigned_none_iff debtBounds).mp unknown_function_cannot_hide_negative_effects

/-! The next input contains a genuinely infinite row. Its two constraints use
the same row code, so the kernel can execute this positive case directly. -/

def recurring : SemilinearRowAlgebra.Row 1 Nat :=
  [(7, [⟨fun _ => 0, [fun _ => 1]⟩])]

def infiniteBounds : Problem 2 (SemilinearRowAlgebra.Row 1 Nat) :=
  [.lower (.arrow (.base .unit) [] (.base .int) recurring) 0,
   .flow 0 1,
   .upper 1 (.arrow (.base .unit) [] (.union (.base .int) (.base .str)) recurring)]

theorem infinite_latent_row_is_solved :
    solveSemilinear infiniteBounds = some (least infiniteBounds) := by
  have checked : accepts SemilinearRowQuotient.compareCodes infiniteBounds
      (least infiniteBounds) = true := by decide +kernel
  simp only [solveSemilinear, solve, checked, ↓reduceIte]

theorem infinite_row_solution_is_least_among_all_set_rows
    (other : Valuation 2 (RecursiveRows.SetRow 1 Nat))
    (model : Models (RecursiveRows.algebra 1 Nat).le (semanticProblem infiniteBounds) other) :
    ∀ target, Subtype (RecursiveRows.algebra 1 Nat).le
      (decodeType (least infiniteBounds target)) (other target) :=
  solveSemilinear_least infinite_latent_row_is_solved model

end Yulang.ValueBoundSolvers.Examples
