import Yulang.CommonCaseLiteralCells
import Yulang.CommonCaseIntegerCoverage
import Yulang.CoreCommonData

/-! An exact finite coverage check for all four inhabited Common literal
bases. Arbitrary source patterns/default callbacks are quantified; a literal
subject never executes a default. Guards do not contribute coverage. -/

namespace Yulang.CommonCaseLiteralCoverage

open LiteralValues (Literal)
open CaseValues EvaluationTrace
open CasePatterns (Pattern)
open CaseEvaluation (Arm)
open CommonCaseLiteralCells (Equivalent SameTexts)

def texts : Pattern Empty D → List String
  | .literal (.str text) => [text]
  | .or first last => texts first ++ texts last
  | .as child _ => texts child
  | _ => []

def accepts : Pattern Empty D → Literal Empty → Bool
  | .wildcard, _ | .bind _, _ => true
  | .literal expected, actual => decide (expected = actual)
  | .intRange lower upper, actual => LiteralValues.intRangeCheck lower upper actual
  | .or first last, actual => accepts first actual || accepts last actual
  | .as child _, actual => accepts child actual
  | _, _ => false

def literalBindings : Pattern Empty D → Literal Empty → Option (Bindings Empty)
  | .wildcard, _ => some []
  | .bind name, actual => some [(name, .literal actual)]
  | .literal expected, actual => if expected = actual then some [] else none
  | .intRange lower upper, actual => if LiteralValues.intRangeCheck lower upper actual then some [] else none
  | .or first last, actual => (literalBindings first actual).orElse (fun _ => literalBindings last actual)
  | .as child name, actual => (literalBindings child actual).map ((name, .literal actual) :: ·)
  | _, _ => none

theorem bindings_isSome (pattern : Pattern Empty D) (actual : Literal Empty) :
    (literalBindings pattern actual).isSome = accepts pattern actual := by
  induction pattern with
  | literal expected => by_cases equal : expected = actual <;> simp [literalBindings, accepts, equal]
  | intRange lower upper =>
      cases checked : LiteralValues.intRangeCheck lower upper actual <;> simp [literalBindings, accepts, checked]
  | or first last ihf ihl =>
      simp only [literalBindings, accepts]
      cases found : literalBindings first actual <;> simp_all
  | as child name ih => simpa only [literalBindings, accepts, Option.isSome_map] using ih
  | _ => rfl

theorem matchCheck_empty (floatCheck : Empty → Empty → Bool) (first last : Literal Empty) :
    LiteralValues.matchCheck floatCheck first last = decide (first = last) := by
  cases first <;> cases last <;> simp [LiteralValues.matchCheck]
  all_goals contradiction

theorem run_literal_exact (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → Logged E R (Value Empty)) (environment : Bindings Empty)
    (pattern : Pattern Empty D) (actual : Literal Empty) :
    ScopedCasePatterns.run floatCheck defaultEval environment pattern (.literal actual) =
      Logged.ofResult (.ok (literalBindings pattern actual)) := by
  induction pattern with
  | wildcard | bind | pair | recordEnd | field | defaultField | nil | cons | snoc | variant | nominal => rfl
  | literal expected =>
      simp only [ScopedCasePatterns.run, matchCheck_empty, literalBindings]
      by_cases equal : expected = actual <;> simp [equal, CasePatterns.success, CasePatterns.miss]
  | intRange lower upper =>
      simp only [ScopedCasePatterns.run, literalBindings]
      cases LiteralValues.intRangeCheck lower upper actual <;> rfl
  | or first last ihf ihl =>
      simp only [ScopedCasePatterns.run, literalBindings, ihf]
      cases literalBindings first actual <;> simp [Logged.bind, Logged.ofResult, ihl, CasePatterns.success]
  | as child name ih =>
      simp only [ScopedCasePatterns.run, literalBindings, ih]
      cases literalBindings child actual <;> simp [Logged.bind, Logged.ofResult, CasePatterns.success, CasePatterns.miss]

theorem matches_literal_exact (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → Logged E R (Value Empty)) (environment : Bindings Empty)
    (pattern : Pattern Empty D) (actual : Literal Empty) :
    (∃ bindings, (ScopedCasePatterns.run floatCheck defaultEval environment pattern (.literal actual)).result = .ok (some bindings)) ↔
      accepts pattern actual = true := by
  simp only [run_literal_exact, Logged.ofResult, Except.ok.injEq]
  rw [← Option.isSome_iff_exists, bindings_isSome]

theorem accepts_integer (pattern : Pattern Empty D) (integer : Int) :
    accepts pattern (.int integer) = CommonCaseIntegerCoverage.accepts pattern integer := by
  induction pattern with
  | literal expected => cases expected <;> simp [accepts, CommonCaseIntegerCoverage.accepts]
  | or first last ihf ihl => simp only [accepts, CommonCaseIntegerCoverage.accepts, ihf, ihl]
  | as child name ih => exact ih
  | _ => rfl

theorem accepts_congr (pattern : Pattern Empty D) (same : Equivalent bounds strings first last)
    (boundsIncluded : ∀ bound ∈ CommonCaseIntegerCoverage.boundaries pattern, bound ∈ bounds)
    (textsIncluded : ∀ text ∈ texts pattern, text ∈ strings) : accepts pattern first = accepts pattern last := by
  induction pattern with
  | wildcard | bind => rfl
  | literal expected =>
      cases same with
      | @integer first last comparisons =>
          rw [accepts_integer, accepts_integer]
          exact CommonCaseIntegerCoverage.accepts_same _ first last (fun bound member => comparisons bound (boundsIncluded bound member))
      | @string first last equalities =>
          cases expected with
          | str text =>
              apply decide_eq_decide.mpr
              simpa only [Literal.str.injEq] using equalities text (textsIncluded text (by simp [texts]))
          | int | bool | unit => rfl
          | float impossible => exact impossible.elim
      | boolean | unit => rfl
  | intRange lower upper =>
      cases same with
      | @integer first last comparisons =>
          rw [accepts_integer, accepts_integer]
          exact CommonCaseIntegerCoverage.accepts_same _ first last (fun bound member => comparisons bound (boundsIncluded bound member))
      | string | boolean | unit => rfl
  | or p q ihp ihq =>
      simp only [accepts,
        ihp (fun bound member => boundsIncluded bound (List.mem_append_left _ member))
          (fun text member => textsIncluded text (List.mem_append_left _ member)),
        ihq (fun bound member => boundsIncluded bound (List.mem_append_right _ member))
          (fun text member => textsIncluded text (List.mem_append_right _ member))]
  | as child name ih => exact ih boundsIncluded textsIncluded
  | _ => rfl

theorem equivalent_base_eq (same : Equivalent bounds strings first last) :
    Core.CommonData.literalBase first = Core.CommonData.literalBase last := by cases same <;> rfl

def armTexts (arms : List (Arm Empty D G B)) : List String := arms.flatMap fun arm => texts arm.pattern

def coversAt (arms : List (Arm Empty D G B)) (actual : Literal Empty) : Bool :=
  arms.any (fun arm => !arm.guard.isSome && accepts arm.pattern actual)

theorem coversAt_exact (arms : List (Arm Empty D G B)) (actual : Literal Empty) :
    coversAt arms actual = true ↔ ∃ arm ∈ arms, arm.guard = none ∧ accepts arm.pattern actual = true := by
  simp only [coversAt, List.any_eq_true, Bool.and_eq_true]
  apply exists_congr
  intro arm
  apply and_congr_right
  intro member
  cases arm.guard <;> simp

private theorem any_congr_on (items : List A) (first last : A → Bool)
    (same : ∀ item ∈ items, first item = last item) : items.any first = items.any last := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.any_cons, same item List.mem_cons_self,
        ih (fun item member => same item (List.mem_cons_of_mem _ member))]

theorem coversAt_congr (arms : List (Arm Empty D G B))
    (same : Equivalent (CommonCaseIntegerCoverage.armBoundaries arms) (armTexts arms) first last) :
    coversAt arms first = coversAt arms last := by
  apply any_congr_on
  intro arm member
  rw [accepts_congr arm.pattern same
    (fun bound present => List.mem_flatMap_of_mem member present)
    (fun text present => List.mem_flatMap_of_mem member present)]

def checkBase (base : Inference.Base) (arms : List (Arm Empty D G B)) : Bool :=
  ((CommonCaseLiteralCells.representatives (CommonCaseIntegerCoverage.armBoundaries arms) (armTexts arms)).filter
    (fun literal => decide (Core.CommonData.literalBase literal = base))).all (coversAt arms)

def BaseCovered (base : Inference.Base) (arms : List (Arm Empty D G B)) : Prop :=
  ∀ actual : Literal Empty, Core.CommonData.literalBase actual = base →
    ∃ arm ∈ arms, arm.guard = none ∧ accepts arm.pattern actual = true

/-- Every actual decoded string, Bool, unit and arbitrary integer, with all
source patterns considered. A finite list of string constants alone cannot
exhaust the string base because the fresh representative is also checked. -/
theorem checkBase_exact (base : Inference.Base) (arms : List (Arm Empty D G B)) :
    checkBase base arms = true ↔ BaseCovered base arms := by
  constructor
  · intro checked actual actualBase
    have all := List.all_eq_true.mp checked
    obtain ⟨sample, member, same⟩ := CommonCaseLiteralCells.representative_complete
      (CommonCaseIntegerCoverage.armBoundaries arms) (armTexts arms) actual
    have sampleBase := (equivalent_base_eq same).trans actualBase
    have accepted := all sample (List.mem_filter.mpr ⟨member, by simpa only [decide_eq_true_eq] using sampleBase⟩)
    rw [coversAt_congr arms same] at accepted
    exact (coversAt_exact arms actual).mp accepted
  · intro covered
    apply List.all_eq_true.mpr
    intro sample member
    have sampleBase := of_decide_eq_true (List.mem_filter.mp member).2
    exact (coversAt_exact arms sample).mpr (covered sample sampleBase)

theorem checkBase_matches_exact (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → Logged E R (Value Empty)) (environment : Bindings Empty)
    (base : Inference.Base) (arms : List (Arm Empty D G B)) :
    checkBase base arms = true ↔ ∀ actual : Literal Empty, Core.CommonData.literalBase actual = base →
      ∃ arm ∈ arms, arm.guard = none ∧ ∃ bindings,
        (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern (.literal actual)).result = .ok (some bindings) := by
  simp only [checkBase_exact, BaseCovered, matches_literal_exact]

namespace Examples

def booleans : List (Arm Empty Empty Empty Unit) :=
  [⟨.literal (.bool false), none, ()⟩, ⟨.literal (.bool true), none, ()⟩]

def strings : List (Arm Empty Empty Empty Unit) :=
  [⟨.literal (.str "yes"), none, ()⟩, ⟨.literal (.str "no"), none, ()⟩]

theorem both_booleans_cover : checkBase .bool booleans = true := by decide
theorem finite_strings_leave_others : checkBase .str strings = false := by decide

end Examples

end Yulang.CommonCaseLiteralCoverage
