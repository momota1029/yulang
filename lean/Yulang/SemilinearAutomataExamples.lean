import Yulang.SemilinearAutomata

/-!
# Semilinear automata regressions

Small executable checks cover the finite construction. Infinite-set examples
use the exact comparison theorem and arithmetic proofs instead of evaluating
the intentionally expensive powerset product. In particular, a target union
may cover the source jointly while neither component contains the source.
-/

namespace Yulang.SemilinearAutomata.Examples

open SemilinearWeights
open SemilinearDigits (Letter)

def scalar (value : Int) : Weight 1 := fun _ => value

def one : Letter 1 := ⟨2, by decide⟩
def digitZero : Letter 1 := ⟨1, by decide⟩

def cancellation : Semi 1 := [⟨scalar 0, [scalar 2, scalar (-3)]⟩]

set_option maxRecDepth 100000 in
theorem short_encoding_keeps_remaining_coefficients :
    FiniteAutomata.checkWord (automaton cancellation) [one] = true := by
  decide

set_option maxRecDepth 100000 in
theorem singleton_padding_accepted :
    FiniteAutomata.checkWord (automaton [Linear.point (scalar 1)]) [one, digitZero, digitZero] = true := by
  decide

theorem empty_below_point : checkSubset ([] : Semi 1) [Linear.point zero] = true := by decide
theorem point_not_below_empty : checkSubset [Linear.point (zero : Weight 1)] [] = false := by decide

theorem duplicate_zero_dimensional_components_equal :
    checkEqual [Linear.point (zero : Weight 0), Linear.point zero] [Linear.point zero] = true := by
  decide

def naturalRay : Semi 1 := [⟨scalar 0, [scalar 1]⟩]
def evenRay : Semi 1 := [⟨scalar 0, [scalar 2]⟩]
def oddRay : Semi 1 := [⟨scalar 1, [scalar 2]⟩]

theorem scalar_ray_exact (base period : Int) (weight : Weight 1) :
    Meaning [⟨scalar base, [scalar period]⟩] weight ↔
      ∃ count : Nat, scalar (base + (count : Int) * period) = weight := by
  rw [meaning_singleton]
  constructor
  · rintro ⟨offset, member, equality⟩
    obtain ⟨count, rfl⟩ := (BinaryCarries.singleton_span (scalar period) offset).mp member
    exact ⟨count, equality⟩
  · rintro ⟨count, equality⟩
    exact ⟨BinaryCarries.scale count (scalar period),
      (BinaryCarries.singleton_span _ _).mpr ⟨count, rfl⟩, equality⟩

theorem naturalRay_exact (weight : Weight 1) :
    Meaning naturalRay weight ↔ ∃ count : Nat, scalar (count : Int) = weight := by
  simpa [naturalRay] using scalar_ray_exact 0 1 weight

/-- The source infinite ray is covered by two residue classes jointly. -/
theorem parity_union_exact (weight : Weight 1) :
    Meaning naturalRay weight ↔ Meaning (evenRay ++ oddRay) weight := by
  rw [naturalRay_exact, meaning_append]
  change (∃ count : Nat, scalar (count : Int) = weight) ↔
    Meaning evenRay weight ∨ Meaning oddRay weight
  rw [show evenRay = [⟨scalar 0, [scalar 2]⟩] from rfl,
    show oddRay = [⟨scalar 1, [scalar 2]⟩] from rfl,
    scalar_ray_exact, scalar_ray_exact]
  constructor
  · rintro ⟨count, rfl⟩
    have choices : count % 2 = 0 ∨ count % 2 = 1 := by omega
    rcases choices with even | odd
    · left
      refine ⟨count / 2, ?_⟩
      funext coordinate
      simp only [scalar]
      omega
    · right
      refine ⟨count / 2, ?_⟩
      funext coordinate
      simp only [scalar]
      omega
  · rintro (⟨count, rfl⟩ | ⟨count, rfl⟩)
    · refine ⟨2 * count, ?_⟩
      funext coordinate
      simp only [scalar, Int.natCast_mul]
      omega
    · refine ⟨2 * count + 1, ?_⟩
      funext coordinate
      simp only [scalar, Int.natCast_mul, Int.natCast_add]
      omega

theorem infinite_union_comparison_accepts : checkEqual naturalRay (evenRay ++ oddRay) = true :=
  (checkEqual_exact _ _).mpr parity_union_exact

/-- Testing inclusion in each target line separately would incorrectly reject
the preceding joint coverage. The comparison algorithm handles the union. -/
theorem neither_residue_class_covers_source :
    checkSubset naturalRay evenRay = false ∧ checkSubset naturalRay oddRay = false := by
  constructor
  · apply (checkSubset_rejects _ _).mpr
    refine ⟨scalar 1, (naturalRay_exact _).mpr ⟨1, rfl⟩, ?_⟩
    intro member
    obtain ⟨count, equality⟩ := (scalar_ray_exact 0 2 _).mp member
    have point := congrFun equality 0
    simp only [scalar] at point
    omega
  · apply (checkSubset_rejects _ _).mpr
    refine ⟨scalar 0, (naturalRay_exact _).mpr ⟨0, rfl⟩, ?_⟩
    intro member
    obtain ⟨count, equality⟩ := (scalar_ray_exact 1 2 _).mp member
    have point := congrFun equality 0
    simp only [scalar] at point
    omega

end Yulang.SemilinearAutomata.Examples
