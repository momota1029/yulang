import Yulang.SemilinearRowAlgebra
import Yulang.SemilinearAutomataExamples

/-!
# Infinite semilinear rows in ground function types

An infinite ray and its two parity classes have different finite encodings.
They nevertheless compare equal, including when the parity classes use
duplicate operation keys. The resulting function types compare in both
directions. The examples use the proved exact decision interfaces rather than
evaluating the intentionally expensive powerset construction.
-/

namespace Yulang.SemilinearRowAlgebra.Examples

open SemilinearWeights
open SemilinearAutomata.Examples (scalar naturalRay evenRay oddRay naturalRay_exact parity_union_exact)

def naturalRow : Row 1 Nat := [(7, naturalRay)]
def parityRow : Row 1 Nat := [(7, evenRay), (7, oddRay)]

theorem parity_meaning (key : Nat) (weight : Weight 1) :
    Meaning naturalRow key weight ↔ Meaning parityRow key weight := by
  by_cases same : key = 7
  · subst key
    simpa [Meaning, naturalRow, parityRow, lookup]
      using parity_union_exact weight
  · simp [Meaning, naturalRow, parityRow, lookup, same]

theorem duplicate_keys_union_infinite_rows : checkEqual naturalRow parityRow = true :=
  (checkEqual_exact _ _).mpr parity_meaning

theorem every_natural_weight_is_retained (count : Nat) :
    Meaning parityRow 7 (scalar (count : Int)) :=
  (parity_meaning 7 _).mp (by
    simpa [Meaning, naturalRow, lookup]
      using (naturalRay_exact _).mpr ⟨count, rfl⟩)

theorem one_parity_class_is_insufficient : checkSubset naturalRow [(7, evenRay)] = false := by
  simpa [checkSubset, support, naturalRow, lookup] using SemilinearAutomata.Examples.neither_residue_class_covers_source.1

theorem different_operation_key_is_not_a_substitute :
    checkSubset naturalRow [(8, naturalRay)] = false := by
  apply (checkSubset_rejects _ _).mpr
  refine ⟨7, scalar 0, ?_, ?_⟩
  · simpa [Meaning, naturalRow, lookup]
      using (naturalRay_exact _).mpr ⟨0, rfl⟩
  · simp [Meaning, lookup]

def naturalFunction : GroundType 1 Nat :=
  .arrow (.base .unit) [] (.base .int) naturalRow

def parityFunction : GroundType 1 Nat :=
  .arrow (.base .unit) [] (.base .int) parityRow

theorem infinite_latent_rows_give_equivalent_function_types :
    equivalentType naturalFunction parityFunction = true := by
  apply (equivalentType_exact _ _).mpr
  constructor
  · exact .arrow (.refl _) (included_refl _) (.refl _)
      (fun key weight => (parity_meaning key weight).mp)
  · exact .arrow (.refl _) (included_refl _) (.refl _)
      (fun key weight => (parity_meaning key weight).mpr)

theorem positive_row_cannot_be_dropped_from_function :
    checkType naturalFunction (.arrow (.base .unit) [] (.base .int) []) = false := by
  have rowRejected : checkSubset naturalRow [] = false := by
    apply (checkSubset_rejects _ _).mpr
    refine ⟨7, scalar 0, ?_, meaning_empty _ _⟩
    simpa [Meaning, naturalRow, lookup]
      using (naturalRay_exact _).mpr ⟨0, rfl⟩
  apply (checkType_rejects _ _).mpr
  intro subtype
  have comparison := StructuralDecisions.Comparison.complete
    (leRow := Included) (fun first second => included_trans first second) subtype
  cases comparison with
  | arrow _ _ _ output =>
      have accepted := (checkSubset_exact naturalRow []).mpr output
      rw [rowRejected] at accepted
      cases accepted
  | record shape _ _ _ => cases shape

end Yulang.SemilinearRowAlgebra.Examples
