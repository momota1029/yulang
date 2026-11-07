import Yulang.CommonPatternTyping

/-!
# Partial correctness of actual structural matches

Unlike DefaultSound, the premise below requires no default to return a value.
Errors are admitted, and only returned values and successful match bindings
are checked. This is not an effect-row or termination theorem.
-/

namespace Yulang.CommonPatternPartialSafety

open CommonPatternTyping
open CommonPatternLookup
open CommonPatternEnvironment (NamedTypes)
open Core.CommonData (Value)
open CasePatterns (Pattern)
open EvaluationTrace (Logged)

def PartialHolds (types : NamedTypes) : Except R (Option (CaseValues.Bindings Empty)) → Prop
  | .error _ => True
  | .ok none => True
  | .ok (some values) => CaseValues.BindingsHold (bindingTypes types) values

def DefaultPartialSound (DefaultTyped : NamedTypes → D → Common.Ty → Prop)
    (defaultEval : CaseValues.Bindings Empty → D → Logged E R Value) : Prop :=
  ∀ types code type, DefaultTyped types code type →
    ∀ environment, CaseValues.BindingsHold (bindingTypes types) environment →
      ∀ value, (defaultEval environment code).result = .ok value → valueAt type value

private theorem andThen_partial (first : CasePatterns.Observation Empty E R)
    (last : CaseValues.Bindings Empty → CasePatterns.Observation Empty E R)
    (firstValid : PartialHolds left first.result)
    (lastValid : ∀ prior, CaseValues.BindingsHold (bindingTypes left) prior →
      PartialHolds right (last prior).result) :
    PartialHolds (left ++ right) (ScopedCasePatterns.andThen first last).result := by
  simp only [ScopedCasePatterns.andThen, Logged.bind_result]
  cases observed : first.result with
  | error error => trivial
  | ok option =>
    rw [observed] at firstValid
    cases option with
    | none => trivial
    | some prior =>
      have rest := lastValid prior firstValid
      simp only [Except.bind, Logged.bind_result]
      cases later : (last prior).result with
      | error error => trivial
      | ok option =>
        rw [later] at rest
        cases option with
        | none => trivial
        | some more =>
          exact (by simpa only [PartialHolds, CasePatterns.success, Logged.ofResult,
            bindingTypes_append] using firstValid.append rest)

/-- Every default code, error/event type, actual outer environment and actual
subject. A successful result has exactly the declared ordered binding types.
Neither success nor failure is assumed in the conclusion. -/
theorem typing_matches_partial (floatCheck : Empty → Empty → Bool)
    (defaultEval : CaseValues.Bindings Empty → D → Logged E R Value)
    (defaults : DefaultPartialSound DefaultTyped defaultEval)
    (typed : Typing DefaultTyped types pattern input bindings) :
    ∀ environment, CaseValues.BindingsHold (bindingTypes types) environment →
      ∀ value, valueAt input value →
        PartialHolds bindings
          (ScopedCasePatterns.run floatCheck defaultEval environment pattern value).result := by
  induction typed with
  | wildcard => intro environment valid value valueValid; exact .nil
  | bind => intro environment valid value valueValid; exact .cons valueValid .nil
  | literal admissible =>
      intro environment valid value valueValid
      cases value <;> simp only [ScopedCasePatterns.run]
      all_goals first
        | (split <;> simp [CasePatterns.success, CasePatterns.miss, Logged.ofResult,
            PartialHolds, bindingTypes, CaseValues.BindingsHold.nil])
        | (exact True.intro)
  | intRange admissible bound =>
      intro environment valid value valueValid
      cases value <;> simp only [ScopedCasePatterns.run]
      all_goals first
        | (split <;> simp [CasePatterns.success, CasePatterns.miss, Logged.ofResult,
            PartialHolds, bindingTypes, CaseValues.BindingsHold.nil])
        | (exact True.intro)
  | pair left right leftIH rightIH =>
      intro environment valid value valueValid
      obtain ⟨first, last, rfl, firstValid, lastValid⟩ :=
        pair_components valueValid _ _ (Common.subtype_refl _)
      simp only [ScopedCasePatterns.run]
      refine andThen_partial _ _ (leftIH environment valid first firstValid) ?_
      intro prior priorValid
      exact rightIH (prior ++ environment)
        (by simpa only [bindingTypes_append] using priorValid.append valid) last lastValid
  | recordEnd =>
      intro environment valid value valueValid
      obtain ⟨fields, rfl⟩ := records_of_width valueValid (Common.subtype_refl _)
      exact .nil
  | field admissible child rest childIH restIH =>
      intro environment valid value valueValid
      have width := Common.subtype_trans admissible
        ((CommonRecordTargetProfiles.subtype_emptyRecord_iff _).mpr rfl)
      obtain ⟨fields, rfl⟩ := records_of_width valueValid width
      obtain ⟨item, found, itemValid⟩ := required_lookup fields _ _ _ valueValid admissible
      simp only [ScopedCasePatterns.run, found]
      refine andThen_partial _ _ (childIH environment valid item itemValid) ?_
      intro prior priorValid
      exact restIH (prior ++ environment)
        (by simpa only [bindingTypes_append] using priorValid.append valid) (.record fields) valueValid
  | @defaultField name input payload types fallback fallbackType p left rest right
      optional fallbackTyped child restTyped childIH restIH =>
      intro environment valid value valueValid
      have width := (CommonRecordTargetProfiles.subtype_emptyRecord_iff input).mpr
        (CommonOptionalBound.optional_payload_shape name input payload optional)
      obtain ⟨fields, rfl⟩ := records_of_width valueValid width
      cases found : CaseValues.lookup name fields with
      | some item =>
        have itemValid := optional_lookup fields _ name payload item valueValid optional found
        rw [ScopedCasePatterns.default_present _ _ _ _ _ _ _ _ _ found]
        refine andThen_partial _ _ (childIH environment valid item ?_) ?_
        · exact typing_change_result itemValid _ (CommonBoundCoalescing.le_union_left _ _)
        · intro prior priorValid
          exact restIH (prior ++ environment)
            (by simpa only [bindingTypes_append] using priorValid.append valid)
            (.record fields) valueValid
      | none =>
        rw [ScopedCasePatterns.default_absent _ _ _ _ _ _ _ _ found, Logged.bind_result]
        cases evaluated : (defaultEval environment fallback).result with
        | error error => trivial
        | ok item =>
          have itemValid := defaults types fallback fallbackType fallbackTyped environment valid item evaluated
          refine andThen_partial _ _ (childIH environment valid item ?_) ?_
          · exact typing_change_result itemValid _ (CommonBoundCoalescing.le_union_right _ _)
          · intro prior priorValid
            exact restIH (prior ++ environment)
              (by simpa only [bindingTypes_append] using priorValid.append valid)
              (.record fields) valueValid
  | variant child childIH =>
      intro environment valid value valueValid
      obtain ⟨item, rfl, itemValid⟩ := variant_payload valueValid _ _ (Common.subtype_refl _)
      simpa [ScopedCasePatterns.run] using childIH environment valid item itemValid
  | or left right leftIH rightIH =>
      intro environment valid value valueValid
      have first := leftIH environment valid value valueValid
      simp only [ScopedCasePatterns.run, Logged.bind_result]
      cases observed : (ScopedCasePatterns.run floatCheck defaultEval environment _ value).result with
      | error error => trivial
      | ok option =>
        rw [observed] at first
        cases option with
        | none => exact rightIH environment valid value valueValid
        | some values => exact first
  | as child childIH =>
      intro environment valid value valueValid
      have matched := childIH environment valid value valueValid
      simp only [ScopedCasePatterns.run, Logged.bind_result]
      cases observed : (ScopedCasePatterns.run floatCheck defaultEval environment _ value).result with
      | error error => trivial
      | ok option =>
        rw [observed] at matched
        cases option with
        | none => trivial
        | some values => exact CaseValues.BindingsHold.cons valueValid matched
  | narrow below child childIH =>
      intro environment valid value valueValid
      exact childIH environment valid value (typing_change_result valueValid _ below)

end Yulang.CommonPatternPartialSafety
