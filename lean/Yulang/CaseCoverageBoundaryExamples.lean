import Yulang.CaseCoverage

/-!
# Concrete limits of the conservative case coverage checker

These examples separate semantic exhaustiveness from the structural judgement
implemented by `CaseCoverage.check`. Three ordinary exhaustive pattern sets
return `false`: a Boolean record field split between two arms, lists split by
length zero/one/at least two, and two complementary unbounded integer ranges.

The positive theorems quantify over actual arbitrary values and execute the
real pattern matcher. They do not assume a successful match, restrict integer
magnitude or bound list length. In particular a negative checker result must
not yet be advertised as a source-language non-exhaustiveness diagnosis.
-/

namespace Yulang.CaseCoverageBoundaryExamples

open CaseValues CasePatterns CaseCoverage LiteralValues EvaluationTrace

variable {F E R : Type}

def noDefaults : Empty → Domain := Empty.elim

def noDefaultEval : Empty → Logged E R (Value F) := Empty.elim

def recordBoolInput : Domain := .required 0 (.base .bool) .records

def recordBoolArms (F : Type) : List (Arm F Empty) :=
  [⟨.field 0 (.literal (.bool false)) .recordEnd, false⟩,
   ⟨.field 0 (.literal (.bool true)) .recordEnd, false⟩]

/-- Field payload cells are not distributed between separate record arms. -/
theorem recordBool_check_false :
    check noDefaults (recordBoolArms F) recordBoolInput = false := rfl

/-- Whichever Boolean is stored in the first matching field, one actual arm
matches the whole original record. Other fields are unrestricted. -/
theorem recordBool_arms_match (floatCheck : F → F → Bool)
    (fields : Bindings F) (flag : Bool)
    (present : lookup 0 fields = some (.literal (.bool flag))) :
    ∃ arm ∈ recordBoolArms F, arm.guarded = false ∧
      run floatCheck (noDefaultEval (E := E) (R := R)) arm.pattern (.record fields) = success [] := by
  cases flag with
  | false =>
      refine ⟨⟨.field 0 (.literal (.bool false)) .recordEnd, false⟩,
        by simp [recordBoolArms], rfl, ?_⟩
      simp [run, present, matchCheck, andThen, success, Logged.ofResult, Logged.bind]
  | true =>
      refine ⟨⟨.field 0 (.literal (.bool true)) .recordEnd, false⟩,
        by simp [recordBoolArms], rfl, ?_⟩
      simp [run, present, matchCheck, andThen, success, Logged.ofResult, Logged.bind]

/-- Every value in the entire required-Boolean-field domain matches an
unguarded arm, despite `recordBool_check_false`. -/
theorem recordBool_semantically_exhaustive (floatCheck : F → F → Bool)
    (value : Value F) (valid : recordBoolInput.denote F value) :
    ∃ arm ∈ recordBoolArms F, arm.guarded = false ∧
      run floatCheck (noDefaultEval (E := E) (R := R)) arm.pattern value = success [] := by
  cases value with
  | record fields =>
      obtain ⟨item, present, itemValid⟩ := valid.1
      cases item with
      | literal actual =>
          cases actual with
          | bool flag => exact recordBool_arms_match floatCheck fields flag present
          | int | float | str | unit => cases itemValid
      | pair | record | variant | nominal | list => cases itemValid
  | literal | pair | variant | nominal | list => cases valid.1

def zeroOneManyArms (F : Type) : List (Arm F Empty) :=
  [⟨.nil, false⟩,
   ⟨.cons (.bind 0) .nil, false⟩,
   ⟨.cons (.bind 0) (.cons (.bind 1) (.bind 2)), false⟩]

/-- The checker does not combine separate arms covering a list tail. -/
theorem zeroOneMany_check_false :
    check noDefaults (zeroOneManyArms F) (.list (.base .int)) = false := rfl

/-- All finite lists, with arbitrary elements, match one of the zero/one/many
arms. In the last case binder 2 receives exactly the remaining tail list. -/
theorem zeroOneMany_arms_match (floatCheck : F → F → Bool)
    (values : List (Value F)) :
    ∃ arm ∈ zeroOneManyArms F, arm.guarded = false ∧ ∃ bindings,
      run floatCheck (noDefaultEval (E := E) (R := R)) arm.pattern (.list values) = success bindings := by
  cases values with
  | nil =>
      exact ⟨⟨.nil, false⟩, by simp [zeroOneManyArms], rfl, [], rfl⟩
  | cons first rest =>
      cases rest with
      | nil =>
          exact ⟨⟨.cons (.bind 0) .nil, false⟩,
            by simp [zeroOneManyArms], rfl, [(0, first)], rfl⟩
      | cons second tail =>
          exact ⟨⟨.cons (.bind 0) (.cons (.bind 1) (.bind 2)), false⟩,
            by simp [zeroOneManyArms], rfl,
            [(0, first), (1, second), (2, .list tail)], rfl⟩

/-- The semantic list statement also holds for every element domain, without
a finite cardinality assumption or a bound on the length of a runtime list. -/
theorem zeroOneMany_semantically_exhaustive (floatCheck : F → F → Bool)
    (element : Domain) (value : Value F) (valid : (Domain.list element).denote F value) :
    ∃ arm ∈ zeroOneManyArms F, arm.guarded = false ∧ ∃ bindings,
      run floatCheck (noDefaultEval (E := E) (R := R)) arm.pattern value = success bindings := by
  cases value with
  | list values => exact zeroOneMany_arms_match floatCheck values
  | literal | pair | record | variant | nominal => cases valid

def splitIntArms (F : Type) : List (Arm F Empty) :=
  [⟨.intRange none (some (-1)), false⟩,
   ⟨.intRange (some 0) none, false⟩]

/-- General integer domains are not split at range boundaries yet. -/
theorem splitInt_check_false :
    check noDefaults (splitIntArms F) (.base .int) = false := rfl

/-- The two closed, one-sided ranges cover every arbitrary-precision integer. -/
theorem splitInt_arms_match (floatCheck : F → F → Bool) (integer : Int) :
    ∃ arm ∈ splitIntArms F, arm.guarded = false ∧
      run floatCheck (noDefaultEval (E := E) (R := R)) arm.pattern (.literal (.int integer)) = success [] := by
  by_cases negative : integer < 0
  · have bounded : integer ≤ -1 := by omega
    refine ⟨⟨.intRange none (some (-1)), false⟩,
      by simp [splitIntArms], rfl, ?_⟩
    simp [run, intRangeCheck, bounded]
  · have nonnegative : 0 ≤ integer := by omega
    refine ⟨⟨.intRange (some 0) none, false⟩,
      by simp [splitIntArms], rfl, ?_⟩
    simp [run, intRangeCheck, nonnegative]

/-- Every value in the semantic integer domain is covered, even though the
current structural checker returns `false` for these two range arms. -/
theorem splitInt_semantically_exhaustive (floatCheck : F → F → Bool)
    (value : Value F) (valid : (Domain.base .int).denote F value) :
    ∃ arm ∈ splitIntArms F, arm.guarded = false ∧
      run floatCheck (noDefaultEval (E := E) (R := R)) arm.pattern value = success [] := by
  cases value with
  | literal actual =>
      cases actual with
      | int integer => exact splitInt_arms_match floatCheck integer
      | float | str | bool | unit => cases valid
  | pair | record | variant | nominal | list => cases valid

end Yulang.CaseCoverageBoundaryExamples
