import Yulang.SolvedRecursiveTypes
import Yulang.SolvedRecursiveRowExamples

/-!
# Type-resolution and semantic-row equality regressions

The small comparisons use kernel evaluation. Cases which identify distinct
quotient representatives use the proved exact interfaces: kernel reduction
can stop at equality transports even though compiled evaluation erases them.
A separate bounded IO check executes those four comparisons and verifies their
Boolean answers; the IO check is not used as evidence for any theorem.

An unrelated unsupported guard does not prevent comparing row-free types,
whereas an occurring unsupported row returns `none`. Exact row equality retains
reference reflexivity even on raw malformed record spines.
-/

namespace Yulang.SolvedRecursiveTypes.Examples

open StructuralBase
open SolvedRecursiveRows.Examples (joined separate single unguardedOdd)
open AutomaticRowSummaries.Examples (blocked odd)

def outputFunction : Ty Nat := .arrow (.base .unit) 9001 (.base .int) 7
def inputFunction : Ty Nat := .arrow (.base .unit) 7 (.base .int) 9001

private theorem target_is_seven (problem : RecursiveRows.Problem n Key Nat)
    (targets : ∀ rule ∈ problem, rule.target = 7)
    (derived : RecursiveRows.Derives problem slot occurrence) : slot = 7 := by
  cases derived with
  | rule member _ => exact targets _ member

private theorem missing_slot_empty (problem : RecursiveRows.Problem n Key Nat)
    (targets : ∀ rule ∈ problem, rule.target = 7) :
    RecursiveRows.Derives problem 9001 = fun _ => False := by
  funext occurrence
  apply propext
  constructor
  · intro derived
    have impossible := target_is_seven problem targets derived
    omega
  · exact False.elim

private theorem arrow_output_included
    {input input' output output' : Ty (RecursiveRows.SetRow n Key)}
    {inputRow inputRow' outputRow outputRow' : RecursiveRows.SetRow n Key}
    (subtype : Subtype (RecursiveRows.algebra n Key).le
      (.arrow input inputRow output outputRow) (.arrow input' inputRow' output' outputRow')) :
    (RecursiveRows.algebra n Key).le outputRow outputRow' := by
  have comparison := StructuralDecisions.Comparison.complete
    (leRow := (RecursiveRows.algebra n Key).le)
    (fun first second occurrence member => second occurrence (first occurrence member)) subtype
  cases comparison with
  | refl => exact fun _ member => member
  | arrow _ _ _ result => exact result
  | record shape _ _ _ => cases shape

private theorem querySubtype_of_supported_answer
    (left right : RecursiveRows.Problem n Nat Nat) (source target : Ty Nat) (answer : Bool)
    (supported : (querySubtype left right source target).isSome = true)
    (exactAnswer : answer = true ↔
      Subtype (RecursiveRows.algebra n Nat).le (meaning left source) (meaning right target)) :
    querySubtype left right source target = some answer := by
  cases returned : querySubtype left right source target with
  | none => simp [returned] at supported
  | some actual =>
      have same : actual = answer := Bool.eq_iff_iff.mpr
        ((querySubtype_exact left right source target actual returned).trans exactAnswer.symm)
      simp [same]

theorem row_free_types_ignore_an_unrelated_active_guard :
    querySubtype blocked blocked (.base .int) (.union (.base .int) (.base .str)) = some true := by
  decide +kernel

theorem row_free_mismatch_is_an_actual_negative_answer :
    querySubtype blocked blocked (.base .int) (.base .str) = some false := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem output_row_is_covariant :
    querySubtype single joined outputFunction outputFunction = some true := by
  apply querySubtype_of_supported_answer _ _ _ _ _ (by decide +kernel)
  constructor
  · intro _
    refine Subtype.arrow (.refl _) ?_ (.refl _) ?_
    · change ∀ occurrence, RecursiveRows.Derives joined 9001 occurrence → _
      rw [missing_slot_empty joined (by simp [SolvedRecursiveRows.Examples.joined])]
      exact fun _ impossible => impossible.elim
    · exact (SolvedRecursiveRows.querySubset_exact single joined 7 7 true
        SolvedRecursiveRows.Examples.extra_operation_key_is_allowed_on_the_right).mp rfl
  · intro _; rfl

set_option maxRecDepth 100000 in
theorem missing_output_operation_is_rejected :
    querySubtype joined single outputFunction outputFunction = some false := by
  apply querySubtype_of_supported_answer _ _ _ _ _ (by decide +kernel)
  simp only [Bool.false_eq_true, false_iff]
  intro subtype
  have output := arrow_output_included subtype
  obtain ⟨occurrence, present, absent⟩ :=
    SolvedRecursiveRows.Examples.missing_operation_has_an_actual_counterexample
  exact absent (output occurrence present)

set_option maxRecDepth 100000 in
theorem input_row_is_contravariant :
    querySubtype joined single inputFunction inputFunction = some true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem an_occurring_active_guard_remains_unsupported :
    querySubtype blocked [] outputFunction outputFunction = none := by
  decide +kernel

def malformedSpine : Ty Nat := .record 4 outputFunction (.base .bool)

set_option maxRecDepth 100000 in
theorem original_row_equality_retains_raw_type_reflexivity :
    queryEquivalent joined separate malformedSpine malformedSpine = some true := by
  have supported : (queryEquivalent joined separate malformedSpine malformedSpine).isSome = true := by
    decide +kernel
  have same : meaning joined malformedSpine = meaning separate malformedSpine := by
    simp only [meaning, malformedSpine, outputFunction, StructuralRowResolution.mapRows]
    rw [SolvedRecursiveRows.Examples.reordered_original_least_solutions_equal,
      missing_slot_empty joined (by simp [SolvedRecursiveRows.Examples.joined]),
      missing_slot_empty separate (by simp [SolvedRecursiveRows.Examples.separate])]
  cases returned : queryEquivalent joined separate malformedSpine malformedSpine with
  | none => simp [returned] at supported
  | some answer =>
      have accepted := (queryEquivalent_exact joined separate malformedSpine malformedSpine
        answer returned).mpr (by rw [same]; exact ⟨.refl _, .refl _⟩)
      simp [accepted]

set_option maxRecDepth 100000 in
theorem infinite_recursive_rows_compare_inside_functions :
    queryEquivalent odd unguardedOdd outputFunction outputFunction = some true := by
  decide +kernel

def point : SemilinearWeights.Semi 0 := [⟨fun index => Fin.elim0 index, []⟩]
def ordered : SemilinearRowAlgebra.Row 0 Nat := [(1, point), (2, point)]
def reordered : SemilinearRowAlgebra.Row 0 Nat := [(2, point), (1, point)]

def rawType (row : SemilinearRowAlgebra.Row 0 Nat) : SemilinearRowAlgebra.GroundType 0 Nat :=
  .record 4 (.arrow (.base .unit) [] (.base .int) row) (.base .bool)

theorem syntax_of_codes_does_not_reflect_raw_set_type_equality :
    SemilinearRowAlgebra.checkType (rawType ordered) (rawType reordered) = false := by
  decide +kernel

theorem quotient_equality_restores_the_reference_reflexive_case :
    SemilinearRowQuotient.compareCodes (rawType ordered) (rawType reordered) = true := by
  have same : SemilinearRowAlgebra.decode ordered = SemilinearRowAlgebra.decode reordered :=
    (SemilinearRowAlgebra.checkEqual_sets ordered reordered).mp (by decide +kernel)
  apply (SemilinearRowQuotient.compareCodes_exact _ _).mpr
  simp only [rawType, StructuralRowResolution.mapRows, same]
  exact .refl _

theorem rejected_latent_effect_has_no_original_subtyping_derivation :
    ¬ Subtype (RecursiveRows.algebra 1 Nat).le
      (meaning joined outputFunction) (meaning single outputFunction) :=
  (querySubtype_rejects joined single outputFunction outputFunction false
    missing_output_operation_is_rejected).mp rfl

#eval do
  if querySubtype single joined outputFunction outputFunction != some true then
    throw (IO.userError "covariant output row comparison failed")
  if querySubtype joined single outputFunction outputFunction != some false then
    throw (IO.userError "missing output operation was not rejected")
  if queryEquivalent joined separate malformedSpine malformedSpine != some true then
    throw (IO.userError "original row equality did not preserve raw type reflexivity")
  if !SemilinearRowQuotient.compareCodes (rawType ordered) (rawType reordered) then
    throw (IO.userError "quotient row equality did not preserve raw type reflexivity")

end Yulang.SolvedRecursiveTypes.Examples
