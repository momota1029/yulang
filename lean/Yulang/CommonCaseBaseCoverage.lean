import Yulang.CommonCaseBaseMatching
import Yulang.CommonCaseIntegerOrdered

/-! Exact finite joint coverage for products and closed variant alternatives
with all four Common literal bases. Integer and string cells remain complete
inside arbitrary nested products. Guarded arms do not count. -/

namespace Yulang.CommonCaseBaseCoverage

open CaseValues EvaluationTrace
open CaseEvaluation (Arm)
open CommonCaseBaseCells (Shape InShape ValueEquivalent representatives)
open CommonCaseBaseMatching (boundaries texts accepts)

def armBoundaries (arms : List (Arm Empty D G B)) : List Int := arms.flatMap fun arm => boundaries arm.pattern

def armTexts (arms : List (Arm Empty D G B)) : List String := arms.flatMap fun arm => texts arm.pattern

def coversAt (arms : List (Arm Empty D G B)) (value : Value Empty) : Bool :=
  arms.any (fun arm => !arm.guard.isSome && accepts arm.pattern value)

private theorem any_congr_on (items : List A) (first last : A → Bool)
    (same : ∀ item ∈ items, first item = last item) : items.any first = items.any last := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.any_cons, same item List.mem_cons_self,
        ih (fun item member => same item (List.mem_cons_of_mem _ member))]

theorem coversAt_congr (arms : List (Arm Empty D G B)) (same : ValueEquivalent (armBoundaries arms) (armTexts arms) first last) :
    coversAt arms first = coversAt arms last := by
  apply any_congr_on
  intro arm member
  rw [CommonCaseBaseMatching.accepts_congr arm.pattern same
    (fun bound present => List.mem_flatMap_of_mem member present)
    (fun text present => List.mem_flatMap_of_mem member present)]

def check (shape : Shape) (arms : List (Arm Empty D G B)) : Bool :=
  (representatives (armBoundaries arms) (armTexts arms) shape).all (coversAt arms)

def Covered (shape : Shape) (arms : List (Arm Empty D G B)) : Prop :=
  ∀ value, InShape shape value → ∃ arm ∈ arms, arm.guard = none ∧ accepts arm.pattern value = true

theorem coversAt_exact (arms : List (Arm Empty D G B)) (value : Value Empty) :
    coversAt arms value = true ↔ ∃ arm ∈ arms, arm.guard = none ∧ accepts arm.pattern value = true := by
  simp only [coversAt, List.any_eq_true, Bool.and_eq_true]
  apply exists_congr
  intro arm
  apply and_congr_right
  intro member
  cases arm.guard <;> simp

/-- Every finite source arm list and every value in an arbitrary finite
nested base/product/variant-choice domain. Guarded arms do not contribute
coverage; no branch count, subject bound, fuel or runtime success is assumed. -/
theorem check_exact (shape : Shape) (arms : List (Arm Empty D G B)) : check shape arms = true ↔ Covered shape arms := by
  simp only [check, List.all_eq_true, Covered, ← coversAt_exact]
  constructor
  · intro checked value valid
    obtain ⟨representative, member, same⟩ := CommonCaseBaseCells.representative_complete (armBoundaries arms) (armTexts arms) valid
    rw [← coversAt_congr arms same]
    exact checked representative member
  · intro covered representative included
    exact covered representative (CommonCaseBaseCells.representatives_sound _ _ _ representative included)

theorem check_matches_exact (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → Logged E R (Value Empty)) (environment : Bindings Empty)
    (shape : Shape) (arms : List (Arm Empty D G B)) :
    check shape arms = true ↔ ∀ value, InShape shape value → ∃ arm ∈ arms, arm.guard = none ∧ ∃ bindings,
      (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).result = .ok (some bindings) := by
  rw [check_exact]
  constructor
  · intro covered value valid
    obtain ⟨arm, member, unguarded, accepted⟩ := covered value valid
    exact ⟨arm, member, unguarded,
      (CommonCaseBaseMatching.matches_supported_exact floatCheck defaultEval environment arm.pattern value valid.supported).mpr accepted⟩
  · intro matched value valid
    obtain ⟨arm, member, unguarded, bindings, observed⟩ := matched value valid
    exact ⟨arm, member, unguarded,
      (CommonCaseBaseMatching.matches_supported_exact floatCheck defaultEval environment arm.pattern value valid.supported).mp ⟨bindings, observed⟩⟩

namespace Examples

def mixedArms : List (Arm Empty Empty Empty Unit) :=
  [⟨.pair (.literal (.bool true)) .wildcard, none, ()⟩,
   ⟨.pair (.literal (.bool false)) (.intRange none (some 0)), none, ()⟩,
   ⟨.pair (.literal (.bool false)) (.intRange (some 1) none), none, ()⟩]

def diagonalArms : List (Arm Empty Empty Empty Unit) :=
  [⟨.pair (.literal (.bool true)) (.intRange none (some 0)), none, ()⟩,
   ⟨.pair (.literal (.bool false)) (.intRange (some 1) none), none, ()⟩]

theorem mixed_product_covered : check (.pair (.base .bool) (.base .int)) mixedArms = true := by decide
theorem mixed_diagonal_rejected : check (.pair (.base .bool) (.base .int)) diagonalArms = false := by decide

end Examples

end Yulang.CommonCaseBaseCoverage
