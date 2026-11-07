import Yulang.CommonCaseStructuralMatching
import Yulang.CommonCaseIntegerOrdered

/-! Exact finite coverage of integer products and closed structural variant
alternatives. Joint cells retain tuple correlations and whole variant tags.
The coverage domain is explicit; its source/Common carrier bridge is separate. -/

namespace Yulang.CommonCaseStructuralCoverage

open CaseValues EvaluationTrace
open CaseEvaluation (Arm)
open CommonCaseStructuralCells (Shape InShape ValueEquivalent representatives)
open CommonCaseStructuralMatching (boundaries accepts)

def armBoundaries (arms : List (Arm F D G B)) : List Int := arms.flatMap fun arm => boundaries arm.pattern

def coversAt (arms : List (Arm F D G B)) (value : Value F) : Bool :=
  arms.any (fun arm => !arm.guard.isSome && accepts arm.pattern value)

private theorem any_congr_on (items : List A) (first last : A → Bool)
    (same : ∀ item ∈ items, first item = last item) : items.any first = items.any last := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.any_cons, same item List.mem_cons_self,
        ih (fun item member => same item (List.mem_cons_of_mem _ member))]

theorem coversAt_congr (arms : List (Arm F D G B)) (same : ValueEquivalent (armBoundaries arms) first last) :
    coversAt arms first = coversAt arms last := by
  apply any_congr_on
  intro arm member
  rw [CommonCaseStructuralMatching.accepts_congr arm.pattern same
    (fun bound present => List.mem_flatMap_of_mem member present)]

def check (shape : Shape) (arms : List (Arm F D G B)) : Bool :=
  (representatives (armBoundaries arms) shape).all (coversAt arms)

def Covered (shape : Shape) (arms : List (Arm F D G B)) : Prop :=
  ∀ value, InShape shape value → ∃ arm ∈ arms, arm.guard = none ∧ accepts arm.pattern value = true

theorem coversAt_exact (arms : List (Arm F D G B)) (value : Value F) :
    coversAt arms value = true ↔ ∃ arm ∈ arms, arm.guard = none ∧ accepts arm.pattern value = true := by
  simp only [coversAt, List.any_eq_true, Bool.and_eq_true]
  apply exists_congr
  intro arm
  apply and_congr_right
  intro member
  cases arm.guard <;> simp

/-- Every finite source arm list and every value in an arbitrary finite
nested integer/product/variant-choice domain. Guarded arms do not contribute
coverage; no branch count, subject bound, fuel or runtime success is assumed. -/
theorem check_exact (shape : Shape) (arms : List (Arm F D G B)) : check shape arms = true ↔ Covered shape arms := by
  simp only [check, List.all_eq_true, Covered, ← coversAt_exact]
  constructor
  · intro checked value valid
    obtain ⟨representative, member, same⟩ := CommonCaseStructuralCells.representative_complete (armBoundaries arms) valid
    rw [← coversAt_congr arms same]
    exact checked representative member
  · intro covered representative included
    exact covered representative (CommonCaseStructuralCells.representatives_sound _ _ representative included)

theorem check_matches_exact (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (environment : Bindings F)
    (shape : Shape) (arms : List (Arm F D G B)) :
    check shape arms = true ↔ ∀ value, InShape shape value → ∃ arm ∈ arms, arm.guard = none ∧ ∃ bindings,
      (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).result = .ok (some bindings) := by
  rw [check_exact]
  constructor
  · intro covered value valid
    obtain ⟨arm, member, unguarded, accepted⟩ := covered value valid
    exact ⟨arm, member, unguarded,
      (CommonCaseStructuralMatching.matches_supported_exact floatCheck defaultEval environment arm.pattern value valid.supported).mpr accepted⟩
  · intro matched value valid
    obtain ⟨arm, member, unguarded, bindings, observed⟩ := matched value valid
    exact ⟨arm, member, unguarded,
      (CommonCaseStructuralMatching.matches_supported_exact floatCheck defaultEval environment arm.pattern value valid.supported).mp ⟨bindings, observed⟩⟩

namespace Examples

def pairArms : List (Arm Empty Empty Empty Unit) :=
  [⟨.pair (.intRange none (some 0)) .wildcard, none, ()⟩,
   ⟨.pair (.intRange (some 1) none) .wildcard, none, ()⟩]

def diagonalArms : List (Arm Empty Empty Empty Unit) :=
  [⟨.pair (.intRange none (some 0)) (.intRange none (some 0)), none, ()⟩,
   ⟨.pair (.intRange (some 1) none) (.intRange (some 1) none), none, ()⟩]

def variantArms : List (Arm Empty Empty Empty Unit) :=
  [⟨.variant 0 (.intRange none (some 0)), none, ()⟩,
   ⟨.variant 0 (.intRange (some 1) none), none, ()⟩,
   ⟨.variant 1 .wildcard, none, ()⟩]

theorem product_jointly_covered : check (.pair .integer .integer) pairArms = true := by decide

theorem diagonal_correlation_retained : check (.pair .integer .integer) diagonalArms = false := by decide

theorem merged_tags_jointly_covered :
    check (.choice (.variant 0 .integer) (.variant 1 .integer)) variantArms = true := by decide

end Examples

end Yulang.CommonCaseStructuralCoverage
