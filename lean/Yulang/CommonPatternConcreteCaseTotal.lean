import Yulang.CommonPatternConcreteCaseSafety
import Yulang.CommonAlignedPatternSafeDefaults
import Yulang.ScopedCaseDataProgram

/-! Error-free safety of the concrete finite data case language. Pattern
misses remain possible; no coverage conclusion is inferred. Every default,
guard and body contract is proved from actual source typing and evaluation. -/

namespace Yulang.CommonPatternConcreteCaseTotal

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration (Comp)
open CommonData (Value)
open CommonPatternEnvironment (NamedTypes)
open CommonPatternTyping (valueAt bindingTypes)
open CommonPatternDataSafety (EnvironmentHolds typing_evaluates prefix_environment)
open CommonPatternConcreteCaseSafety (defaults defaults_invariant)
open CommonPatternSourceElaboration (DefaultTyped)
open CommonPatternSourceScope (corePrefix)
open CommonPatternSourceArmGeneration (EnvironmentTyping GuardTyping)
open CommonPatternSourceArmsSolved (SourceArm)
open CaseValues (Bindings BindingsHold)
open CaseEvaluation (ResultHolds)
open EvaluationTrace (Logged)

@[local simp] private theorem except_bind_ok (value : A) (next : A → Except R B) :
    (Except.ok value).bind next = next value := rfl

theorem default_sound (outer : EnvironmentHolds outerNames environment actualOuter) :
    CommonPatternTyping.DefaultSound (DefaultTyped outerNames environment) (defaults actualOuter) := by
  intro types code type typed actual valid
  obtain ⟨row, typed⟩ := typed
  obtain ⟨value, evaluated, safe⟩ := typing_evaluates code _ _ _ _ (prefix_environment types actual valid outer) typed
  exact ⟨value, evaluated,
    CommonPatternLookup.typing_change_result safe (Comp.pure Common.model type) (Common.subtype_refl _)⟩

theorem body_sound (outer : EnvironmentHolds outerNames environment actualOuter)
    (types : NamedTypes) (code : CaseDataTerms.Expr Empty) (result : Comp Common.model)
    (typed : CommonSyntax.Typing Common.model (corePrefix types ++ environment)
      (Data.embed (types.map Prod.fst ++ outerNames) code) result)
    (actual : Bindings Empty) (valid : BindingsHold (bindingTypes types) actual) :
    ∃ value, (CaseDataTerms.bodyEval actualOuter code actual).result = .ok value ∧ valueAt result.1 value := by
  obtain ⟨value, evaluated, safe⟩ := typing_evaluates code _ _ _ _ (prefix_environment types actual valid outer) typed
  exact ⟨value, evaluated,
    CommonPatternLookup.typing_change_result safe (Comp.pure Common.model result.1) (Common.subtype_refl _)⟩

theorem guard_sound (outer : EnvironmentHolds outerNames environment actualOuter)
    (types : NamedTypes) (code : CaseDataTerms.Expr Empty) (row : Common.Row)
    (typed : CommonSyntax.Typing Common.model (corePrefix types ++ environment)
      (Data.embed (types.map Prod.fst ++ outerNames) code) (.base .bool, row))
    (actual : Bindings Empty) (valid : BindingsHold (bindingTypes types) actual) :
    ∃ accepted, (CaseDataTerms.guardEval actualOuter code actual).result = .ok accepted := by
  obtain ⟨value, evaluated, safe⟩ := typing_evaluates code _ _ _ _ (prefix_environment types actual valid outer) typed
  obtain ⟨literal, rfl, scalar⟩ := CommonPatternLookup.literal_of_base safe .bool (Common.subtype_refl _)
  cases literal with
  | bool accepted =>
      exact ⟨accepted, by simp [CaseDataTerms.guardEval, Logged.bind_result, evaluated, Logged.ofResult]⟩
  | int | str | unit => cases scalar
  | float value => exact value.elim

theorem testArm_safe (outer : EnvironmentHolds outerNames environment actualOuter)
    (floatCheck : Empty → Empty → Bool) (arm : SourceArm)
    (patternTyped : CommonAlignedPatternTyping.Typing (DefaultTyped outerNames environment) [] arm.pattern input bindings)
    (guardTyped : GuardTyping (corePrefix bindings ++ environment) (bindings.map Prod.fst ++ outerNames) arm.guard guardRow)
    (value : Value) (valid : valueAt input value) (index : Nat) :
    CasePatterns.Holds (bindingTypes bindings)
      (CommonAlignedCaseEvaluation.testArm floatCheck (defaults actualOuter) []
        (CaseDataTerms.guardEval actualOuter) index arm value).result := by
  have safe := CommonAlignedPatternSafeDefaults.typing_matches floatCheck (defaults actualOuter) (default_sound outer)
    patternTyped.2 patternTyped.1 [] .nil value valid
  simp only [CommonAlignedCaseEvaluation.testArm, Logged.bind_result]
  cases observed : (CommonPatternAlignedMatcher.run floatCheck (defaults actualOuter) [] arm.pattern value).result with
  | error => rw [observed] at safe; exact safe
  | ok option =>
      rw [observed] at safe
      cases option with
      | none => trivial
      | some actual =>
          cases guard : arm.guard with
          | none => exact safe
          | some code =>
              have typed : CommonSyntax.Typing Common.model (corePrefix bindings ++ environment)
                  (Data.embed (bindings.map Prod.fst ++ outerNames) code) (.base .bool, guardRow) := by
                simpa only [GuardTyping, guard] using guardTyped
              obtain ⟨accepted, evaluated⟩ := guard_sound outer bindings code guardRow typed actual safe
              simp only [except_bind_ok, Logged.prepend_result, Logged.bind_result, evaluated]
              cases accepted <;> first | trivial | exact safe

theorem canonical_runArms_safe (outer : EnvironmentHolds outerNames environment actualOuter)
    (arms : List SourceArm)
    (typed : ∀ arm ∈ arms, ∃ guardRow,
      EnvironmentTyping outerNames environment arm.pattern arm.guard arm.body input guardRow result)
    (floatCheck : Empty → Empty → Bool) (value : Value) (valid : valueAt input value) (index : Nat) :
    ResultHolds (valueAt result.1)
      (CommonAlignedCaseEvaluation.runArms floatCheck (defaults actualOuter) []
        (CaseDataTerms.guardEval actualOuter) (CaseDataTerms.bodyEval actualOuter) value index arms).result := by
  induction arms generalizing index with
  | nil => trivial
  | cons arm rest ih =>
      obtain ⟨guardRow, armTyped⟩ := typed arm List.mem_cons_self
      cases armTyped with
      | arm patternTyped guardTyped bodyTyped =>
          have safe := testArm_safe outer floatCheck arm patternTyped guardTyped value valid index
          simp only [CommonAlignedCaseEvaluation.runArms, Logged.prepend_result, Logged.bind_result]
          cases observed : (CommonAlignedCaseEvaluation.testArm floatCheck (defaults actualOuter) []
              (CaseDataTerms.guardEval actualOuter) index arm value).result with
          | error => rw [observed] at safe; exact safe
          | ok option =>
              rw [observed] at safe
              cases option with
              | none => exact ih (fun arm member => typed arm (List.mem_cons_of_mem _ member)) (index + 1)
              | some actual =>
                  obtain ⟨output, evaluated, outputType⟩ := body_sound outer _ _ _ bodyTyped actual safe
                  simpa only [except_bind_ok, Logged.prepend_result, Logged.bind_result, evaluated, Logged.ofResult,
                    ResultHolds] using outputType

/-- Every captured logical environment and every finite typed source arm
list. The original concrete evaluator cannot return a runtime data error;
an unmatched case remains `.ok none` until coverage is separately proved. -/
theorem actual_runArms_safe (outer : EnvironmentHolds outerNames environment actualOuter)
    (arms : List SourceArm)
    (typed : ∀ arm ∈ arms, ∃ guardRow,
      EnvironmentTyping outerNames environment arm.pattern arm.guard arm.body input guardRow result)
    (floatCheck : Empty → Empty → Bool) (value : Value) (valid : valueAt input value) (index : Nat) :
    ResultHolds (valueAt result.1)
      (ScopedCaseEvaluation.runArms floatCheck CaseDataTerms.defaultEval actualOuter
        (CaseDataTerms.guardEval actualOuter) (CaseDataTerms.bodyEval actualOuter) value index arms).result := by
  have sourceValid : ∀ arm ∈ arms, PatternBindingChecks.NamesValid arm.pattern := by
    intro arm member
    obtain ⟨guardRow, armTyped⟩ := typed arm member
    cases armTyped with | arm patternTyped guardTyped bodyTyped => exact patternTyped.1
  have safe := canonical_runArms_safe outer arms typed floatCheck value valid index
  rw [CommonAlignedCaseEvaluation.runArms_eq floatCheck (defaults actualOuter) (defaults_invariant actualOuter)
    [] [] (fun _ => rfl) (CaseDataTerms.guardEval actualOuter) (CommonAlignedCaseEvaluation.data_guard_invariant actualOuter)
    (CaseDataTerms.bodyEval actualOuter) (CommonAlignedCaseEvaluation.data_body_invariant actualOuter)
    value index arms sourceValid] at safe
  have captured := CommonPatternCapturedEvaluation.runArms_capture floatCheck CaseDataTerms.defaultEval actualOuter []
    (CaseDataTerms.guardEval actualOuter) (CaseDataTerms.bodyEval actualOuter) value index arms
  have same : CommonPatternCapturedEvaluation.capture CaseDataTerms.defaultEval actualOuter = defaults actualOuter := rfl
  simp only [List.nil_append, same] at captured
  rw [captured]
  exact safe

theorem returned_scheme_safe (outerNames : List Nat) (arms : List SourceArm)
    (scheme : CommonPatternFiniteSchemes.Scheme 3)
    (returned : scheme ∈ CommonPatternSourceArmsSolved.infer outerNames arms) (parameters : scheme.Parameters)
    (floatCheck : Empty → Empty → Bool) (value : Value)
    (valid : valueAt (scheme.instantiate parameters 0).1 value) (index : Nat) :
    ResultHolds (valueAt (scheme.instantiate parameters 2).1)
      (ScopedCaseEvaluation.runArms floatCheck CaseDataTerms.defaultEval []
        (CaseDataTerms.guardEval []) (CaseDataTerms.bodyEval []) value index arms).result :=
  actual_runArms_safe (EnvironmentHolds.nil outerNames []) arms
    (fun arm member => ⟨_, CommonPatternSourceArmsSolved.all_parameter_environments
      outerNames arms scheme returned parameters arm member⟩) floatCheck value valid index

/-- The subject is the actual typed source expression and is evaluated once.
This reaches the concrete source-program evaluator, with arbitrary captured
logical environments; absence of a selected arm is still allowed. -/
theorem program_safe (outer : EnvironmentHolds outerNames environment actualOuter)
    (program : CaseDataProgram.Program Empty) (subject : Comp Common.model)
    (subjectTyped : CommonSyntax.Typing Common.model environment (Data.embed outerNames program.scrutinee) subject)
    (typed : ∀ arm ∈ program.arms, ∃ guardRow,
      EnvironmentTyping outerNames environment arm.pattern arm.guard arm.body subject.1 guardRow result)
    (floatCheck : Empty → Empty → Bool) :
    ResultHolds (valueAt result.1) (ScopedCaseDataProgram.eval floatCheck actualOuter program).result := by
  obtain ⟨value, evaluated, safe⟩ := typing_evaluates program.scrutinee outerNames environment actualOuter subject outer subjectTyped
  have valueTyped := CommonPatternLookup.typing_change_result safe (Comp.pure Common.model subject.1) (Common.subtype_refl _)
  have selected := actual_runArms_safe outer program.arms typed floatCheck value valueTyped 0
  simpa only [ScopedCaseDataProgram.eval, ScopedCaseEvaluation.eval, Logged.prepend_result,
    Logged.bind_result, evaluated, except_bind_ok] using selected

end Yulang.CommonPatternConcreteCaseTotal
