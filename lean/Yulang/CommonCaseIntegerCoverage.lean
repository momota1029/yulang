import Yulang.CommonCaseIntegerCells
import Yulang.CommonCaseOrderedPaths

/-! Exact coverage of every integer by arbitrary finite unions of scalar
source ranges/literals, including nested or/as. Guards never count toward
coverage. Structured patterns simply miss an integer subject. The original
conservative structural checker is left unchanged. -/

namespace Yulang.CommonCaseIntegerCoverage

open CaseValues EvaluationTrace
open CasePatterns (Pattern)
open CaseEvaluation (Arm)
open CommonCaseIntegerCells (SameComparisons representatives)

def boundaries : Pattern F D → List Int
  | .literal (.int integer) => [integer]
  | .intRange lower upper => lower.toList ++ upper.toList
  | .or first last => boundaries first ++ boundaries last
  | .as child _ => boundaries child
  | _ => []

def accepts : Pattern F D → Int → Bool
  | .wildcard, _ | .bind _, _ => true
  | .literal (.int expected), integer => decide (expected = integer)
  | .intRange lower upper, integer => LiteralValues.intRangeCheck lower upper (.int integer : LiteralValues.Literal F)
  | .or first last, integer => accepts first integer || accepts last integer
  | .as child _, integer => accepts child integer
  | _, _ => false

def integerBindings : Pattern F D → Int → Option (Bindings F)
  | .wildcard, _ => some []
  | .bind name, integer => some [(name, .literal (.int integer))]
  | .literal (.int expected), integer => if expected = integer then some [] else none
  | .intRange lower upper, integer =>
      if LiteralValues.intRangeCheck lower upper (.int integer : LiteralValues.Literal F) then some [] else none
  | .or first last, integer => (integerBindings first integer).orElse (fun _ => integerBindings last integer)
  | .as child name, integer => (integerBindings child integer).map ((name, .literal (.int integer)) :: ·)
  | _, _ => none

theorem bindings_isSome (pattern : Pattern F D) (integer : Int) :
    (integerBindings pattern integer).isSome = accepts pattern integer := by
  induction pattern with
  | literal expected =>
      cases expected with
      | int expected => by_cases same : expected = integer <;> simp [integerBindings, accepts, same]
      | float | str | bool | unit => rfl
  | intRange lower upper =>
      cases checked : LiteralValues.intRangeCheck lower upper (.int integer : LiteralValues.Literal F) <;>
        simp [integerBindings, accepts, checked]
  | or first last ihf ihl =>
      simp only [integerBindings, accepts]
      cases found : integerBindings first integer <;> simp_all
  | as child name ih => simpa only [integerBindings, accepts, Option.isSome_map] using ih
  | _ => rfl

/-- All source patterns, arbitrary default callbacks/environments, arbitrary
integer values. No callback is evaluated by an integer match; the entire
trace is empty and the real binding list is preserved literally. -/
theorem run_integer_exact (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (environment : Bindings F)
    (pattern : Pattern F D) (integer : Int) :
    ScopedCasePatterns.run floatCheck defaultEval environment pattern (.literal (.int integer)) =
      Logged.ofResult (.ok (integerBindings pattern integer)) := by
  induction pattern with
  | wildcard | bind | pair | recordEnd | field | defaultField | nil | cons | snoc | variant | nominal => rfl
  | literal expected =>
      cases expected <;> simp [ScopedCasePatterns.run, LiteralValues.matchCheck, integerBindings,
        CasePatterns.success, CasePatterns.miss, Logged.ofResult]
      split <;> rfl
  | intRange lower upper =>
      simp only [ScopedCasePatterns.run, integerBindings]
      cases LiteralValues.intRangeCheck lower upper (.int integer : LiteralValues.Literal F) <;> rfl
  | or first last ihf ihl =>
      simp only [ScopedCasePatterns.run, ihf, integerBindings]
      cases integerBindings first integer <;>
        simp [Logged.bind, Logged.ofResult, CasePatterns.success, ihl]
  | as child name ih =>
      simp only [ScopedCasePatterns.run, ih, integerBindings]
      cases integerBindings child integer <;>
        simp [Logged.bind, Logged.ofResult, CasePatterns.success, CasePatterns.miss]

theorem matches_integer_exact (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (environment : Bindings F)
    (pattern : Pattern F D) (integer : Int) :
    (∃ bindings, (ScopedCasePatterns.run floatCheck defaultEval environment pattern (.literal (.int integer))).result =
      .ok (some bindings)) ↔ accepts pattern integer = true := by
  simp only [run_integer_exact, Logged.ofResult, Except.ok.injEq]
  rw [← Option.isSome_iff_exists, bindings_isSome]

theorem accepts_same (pattern : Pattern F D) (first last : Int)
    (same : SameComparisons (boundaries pattern) first last) : accepts pattern first = accepts pattern last := by
  induction pattern with
  | literal expected =>
      cases expected with
      | int bound =>
          have comparison := same bound (by simp [boundaries])
          have equal : (bound = first) ↔ (bound = last) := by omega
          exact decide_eq_decide.mpr equal
      | float | str | bool | unit => rfl
  | intRange lower upper =>
      cases lower with
      | none =>
          cases upper with
          | none => rfl
          | some bound =>
              have comparison := (same bound (by simp [boundaries])).2
              simpa only [accepts, LiteralValues.intRangeCheck, Bool.true_and] using decide_eq_decide.mpr comparison
      | some lower =>
          have low := (same lower (by simp [boundaries])).1
          cases upper with
          | none =>
              simpa only [accepts, LiteralValues.intRangeCheck, Bool.and_true] using decide_eq_decide.mpr low
          | some upper =>
              have high := (same upper (by simp [boundaries])).2
              simp only [accepts, LiteralValues.intRangeCheck, decide_eq_decide.mpr low, decide_eq_decide.mpr high]
  | or p q ihp ihq =>
      have left : SameComparisons (boundaries p) first last := fun bound member => same bound (List.mem_append_left _ member)
      have right : SameComparisons (boundaries q) first last := fun bound member => same bound (List.mem_append_right _ member)
      simp only [accepts, ihp left, ihq right]
  | as child name ih => exact ih same
  | _ => rfl

def armBoundaries (arms : List (Arm F D G B)) : List Int := arms.flatMap fun arm => boundaries arm.pattern

def coversAt (arms : List (Arm F D G B)) (integer : Int) : Bool :=
  arms.any (fun arm => !arm.guard.isSome && accepts arm.pattern integer)

private theorem any_congr_on (items : List A) (first last : A → Bool)
    (same : ∀ item ∈ items, first item = last item) : items.any first = items.any last := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.any_cons, same item List.mem_cons_self,
        ih (fun item member => same item (List.mem_cons_of_mem _ member))]

theorem coversAt_same (arms : List (Arm F D G B)) (first last : Int)
    (same : SameComparisons (armBoundaries arms) first last) : coversAt arms first = coversAt arms last := by
  apply any_congr_on
  intro arm member
  have patternSame : SameComparisons (boundaries arm.pattern) first last := fun bound present =>
    same bound (List.mem_flatMap_of_mem member present)
  rw [accepts_same arm.pattern first last patternSame]

def checkInteger (arms : List (Arm F D G B)) : Bool :=
  (representatives (armBoundaries arms)).all (coversAt arms)

def IntegerCovered (arms : List (Arm F D G B)) : Prop :=
  ∀ integer, ∃ arm ∈ arms, arm.guard = none ∧ accepts arm.pattern integer = true

theorem coversAt_exact (arms : List (Arm F D G B)) (integer : Int) :
    coversAt arms integer = true ↔ ∃ arm ∈ arms, arm.guard = none ∧ accepts arm.pattern integer = true := by
  simp only [coversAt, List.any_eq_true, Bool.and_eq_true]
  apply exists_congr
  intro arm
  apply and_congr_right
  intro member
  cases arm.guard <;> simp

/-- All finite source arm lists and all integers. Endpoints and their two
neighbors are a complete finite partition for arbitrary overlapping,
disjoint, bounded and unbounded integer interval unions. -/
theorem checkInteger_exact (arms : List (Arm F D G B)) : checkInteger arms = true ↔ IntegerCovered arms := by
  simp only [checkInteger, List.all_eq_true, IntegerCovered, ← coversAt_exact]
  constructor
  · intro checked integer
    obtain ⟨representative, included, same⟩ := CommonCaseIntegerCells.representative_exact (armBoundaries arms) integer
    rw [← coversAt_same arms representative integer same]
    exact checked representative included
  · intro covered representative included
    exact covered representative

/-- The coverage computation reaches the real scoped matcher with arbitrary
callbacks. Guarded arms do not count; no successful default assumption or
already-chosen arm is a premise. First-match execution is handled separately. -/
theorem checkInteger_matches_exact (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (environment : Bindings F)
    (arms : List (Arm F D G B)) :
    checkInteger arms = true ↔
      ∀ integer, ∃ arm ∈ arms, arm.guard = none ∧ ∃ bindings,
        (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern (.literal (.int integer))).result =
          .ok (some bindings) := by
  simp only [checkInteger_exact, IntegerCovered, matches_integer_exact]

namespace Examples

def splitArms : List (Arm Empty Empty Empty Unit) :=
  [⟨.intRange none (some 0), none, ()⟩, ⟨.intRange (some 1) none, none, ()⟩]

def gapArms : List (Arm Empty Empty Empty Unit) :=
  [⟨.intRange none (some 0), none, ()⟩, ⟨.intRange (some 2) none, none, ()⟩]

theorem split_exhaustive : checkInteger splitArms = true := by decide

theorem gap_rejected : checkInteger gapArms = false := by decide

theorem guarded_half_not_counted :
    checkInteger (G := Unit) [⟨.intRange (F := Empty) (Default := Empty) none (some 0), none, ()⟩,
      ⟨.intRange (some 1) none, some (), ()⟩] = false := by decide

end Examples

end Yulang.CommonCaseIntegerCoverage
