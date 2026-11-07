import Yulang.CommonCaseRecordMatching

/-! Exact joint coverage of required-field record domains by pure patterns.
The domain permits arbitrary extra fields and duplicate actual/specification
labels. This does not yet count an executable default toward coverage. -/

namespace Yulang.CommonCaseRecordCoverage

open CaseValues EvaluationTrace
open CaseEvaluation (Arm)
open CommonCaseRecordCells (Specification Domain representatives)
open CommonCaseRecordMatching (accepts)

def armBoundaries (arms : List (Arm Empty Empty G B)) : List Int :=
  arms.flatMap fun arm => CommonCaseBaseMatching.boundaries arm.pattern

def armTexts (arms : List (Arm Empty Empty G B)) : List String :=
  arms.flatMap fun arm => CommonCaseBaseMatching.texts arm.pattern

def coversAt (floatCheck : Empty → Empty → Bool) (arms : List (Arm Empty Empty G B)) (fields : Bindings Empty) : Bool :=
  arms.any fun arm => !arm.guard.isSome && accepts floatCheck arm.pattern (.record fields)

theorem coversAt_exact (floatCheck : Empty → Empty → Bool) (arms : List (Arm Empty Empty G B)) (fields : Bindings Empty) :
    coversAt floatCheck arms fields = true ↔ ∃ arm ∈ arms, arm.guard = none ∧ accepts floatCheck arm.pattern (.record fields) = true := by
  simp only [coversAt, List.any_eq_true, Bool.and_eq_true]
  apply exists_congr
  intro arm
  apply and_congr_right
  intro member
  cases arm.guard <;> simp

def check (floatCheck : Empty → Empty → Bool) (specification : Specification) (arms : List (Arm Empty Empty G B)) : Bool :=
  (representatives (armBoundaries arms) (armTexts arms) specification).all (coversAt floatCheck arms)

def Covered (floatCheck : Empty → Empty → Bool) (specification : Specification) (arms : List (Arm Empty Empty G B)) : Prop :=
  ∀ fields, Domain specification fields → ∃ arm ∈ arms, arm.guard = none ∧ accepts floatCheck arm.pattern (.record fields) = true

/-- Finite minimal records suffice for every domain record, not merely
records with the same fields. The reverse direction checks actual domain
members and therefore also covers empty/inconsistent specifications. -/
theorem check_exact (floatCheck : Empty → Empty → Bool) (specification : Specification) (arms : List (Arm Empty Empty G B)) :
    check floatCheck specification arms = true ↔ Covered floatCheck specification arms := by
  constructor
  · intro checked fields valid
    obtain ⟨samples, member, related⟩ := CommonCaseRecordCells.representative_complete
      (armBoundaries arms) (armTexts arms) specification fields valid
    obtain ⟨arm, armMember, unguarded, accepted⟩ := (coversAt_exact floatCheck arms samples).mp
      (List.all_eq_true.mp checked samples member)
    exact ⟨arm, armMember, unguarded, CommonCaseRecordMatching.record_accepts_transfer floatCheck arm.pattern related
      (fun bound present => List.mem_flatMap_of_mem armMember present)
      (fun text present => List.mem_flatMap_of_mem armMember present) accepted⟩
  · intro covered
    apply List.all_eq_true.mpr
    intro samples member
    exact (coversAt_exact floatCheck arms samples).mpr
      (covered samples (CommonCaseRecordCells.representatives_sound _ _ _ samples member))

theorem check_matches_exact (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → Empty → Logged E R (Value Empty)) (environment : Bindings Empty)
    (specification : Specification) (arms : List (Arm Empty Empty G B)) :
    check floatCheck specification arms = true ↔ ∀ fields, Domain specification fields →
      ∃ arm ∈ arms, arm.guard = none ∧ ∃ returned,
        (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern (.record fields)).result = .ok (some returned) := by
  simp only [check_exact, Covered, CommonCaseRecordMatching.matches_exact]

namespace Examples

def specification : Specification := [(0, .base .bool), (1, .base .bool)]

def splitArms : List (Arm Empty Empty Empty Unit) :=
  [⟨.field 0 (.literal (.bool true)) .recordEnd, none, ()⟩,
   ⟨.field 0 (.literal (.bool false)) .recordEnd, none, ()⟩]

def diagonalArms : List (Arm Empty Empty Empty Unit) :=
  [⟨.field 0 (.literal (.bool true)) (.field 1 (.literal (.bool true)) .recordEnd), none, ()⟩,
   ⟨.field 0 (.literal (.bool false)) (.field 1 (.literal (.bool false)) .recordEnd), none, ()⟩]

theorem record_split_covers_extras : check Empty.elim specification splitArms = true := by decide
theorem record_diagonal_retains_correlation : check Empty.elim specification diagonalArms = false := by decide

end Examples

end Yulang.CommonCaseRecordCoverage
