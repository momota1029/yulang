import Yulang.CommonPatternDataSafety
import Yulang.CommonPatternSourceArmsSolved
import Yulang.CommonPatternCapturedEvaluation

/-! Concrete finite data callbacks discharge the successful-return contracts
used by source ordered-case partial safety. No arbitrary effectful leaf is
assumed terminating. Coverage and aggregate operation rows remain separate. -/

namespace Yulang.CommonPatternConcreteCaseSafety

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration (Comp)
open CommonData (Value)
open CaseValues (Bindings)
open CommonPatternDataSafety (EnvironmentHolds typing_evaluates prefix_environment)
open CommonPatternSourceCasePartial (BodyPartialSound PartialResult)
open CommonPatternSourceElaboration (DefaultTyped)

def defaults (outer : Bindings Empty) (preceding : Bindings Empty) (code : CaseDataTerms.Expr Empty) :=
  CaseDataTerms.eval (preceding ++ outer) code

/-- Captured environments retain all instances. Each actual Q4 prefix is
validated at the same ordered mono types used by source default typing. -/
theorem default_partial_sound (outer : EnvironmentHolds outerNames environment actualOuter) :
    CommonPatternPartialSafety.DefaultPartialSound (DefaultTyped outerNames environment) (defaults actualOuter) := by
  intro types code type typed actual valid value returned
  obtain ⟨row, typed⟩ := typed
  obtain ⟨result, evaluated, safe⟩ := typing_evaluates code _ _ _ _
    (prefix_environment types actual valid outer) typed
  have same : result = value := Except.ok.inj (evaluated.symm.trans returned)
  subst result
  exact CommonPatternLookup.typing_change_result safe (Comp.pure Common.model type) (Common.subtype_refl _)

theorem body_partial_sound (outer : EnvironmentHolds outerNames environment actualOuter) :
    BodyPartialSound outerNames environment (CaseDataTerms.bodyEval actualOuter) := by
  intro types code result typed actual valid value returned
  obtain ⟨output, evaluated, safe⟩ := typing_evaluates code _ _ _ _
    (prefix_environment types actual valid outer) typed
  have same : output = value := Except.ok.inj (evaluated.symm.trans returned)
  subst output
  exact CommonPatternLookup.typing_change_result safe (Comp.pure Common.model result.1) (Common.subtype_refl _)

theorem defaults_invariant (outer : Bindings Empty) : CommonPatternAlignedMatcher.DefaultInvariant (defaults outer) := by
  intro first last same code
  exact CommonPatternBindingAlignment.data_eval_lookup_eq code _ _ (same.append outer)

/-- Actual named outer runtime environments, arbitrary captured instances,
all finite source arms and all successful values. The closure-capture bridge
is proved for the actual matcher, including default errors and failed or
branches; no callback correctness premise remains. -/
theorem actual_runArms_partial (outer : EnvironmentHolds outerNames environment actualOuter)
    (arms : List CommonPatternSourceArmsSolved.SourceArm)
    (typed : ∀ arm ∈ arms, ∃ guardRow,
      CommonPatternSourceArmGeneration.EnvironmentTyping outerNames environment
        arm.pattern arm.guard arm.body input guardRow result)
    (floatCheck : Empty → Empty → Bool) (value : Value)
    (valid : CommonPatternTyping.valueAt input value) (index : Nat) :
    PartialResult result.1
      (ScopedCaseEvaluation.runArms floatCheck CaseDataTerms.defaultEval actualOuter
        (CaseDataTerms.guardEval actualOuter) (CaseDataTerms.bodyEval actualOuter) value index arms).result := by
  have safe := CommonPatternSourceCasePartial.actual_runArms_partial floatCheck (defaults actualOuter)
    (default_partial_sound outer) (defaults_invariant actualOuter)
    (CaseDataTerms.guardEval actualOuter) (CommonAlignedCaseEvaluation.data_guard_invariant actualOuter)
    (CaseDataTerms.bodyEval actualOuter) (body_partial_sound outer) (CommonAlignedCaseEvaluation.data_body_invariant actualOuter)
    arms typed value valid index
  have captured := CommonPatternCapturedEvaluation.runArms_capture floatCheck CaseDataTerms.defaultEval actualOuter []
    (CaseDataTerms.guardEval actualOuter) (CaseDataTerms.bodyEval actualOuter) value index arms
  have same : CommonPatternCapturedEvaluation.capture CaseDataTerms.defaultEval actualOuter = defaults actualOuter := rfl
  simp only [List.nil_append, same] at captured
  rw [captured]
  exact safe

/-- The real finite solved source-arm list and every unrestricted parameter
product imply success-value safety of actual ordered evaluation on the
concrete finite data callbacks. No callback correctness/success oracle is a
premise. This remains the empty-captured-environment arm factor of B2. -/
theorem returned_scheme_partial (outerNames : List Nat) (arms : List CommonPatternSourceArmsSolved.SourceArm)
    (scheme : CommonPatternFiniteSchemes.Scheme 3)
    (returned : scheme ∈ CommonPatternSourceArmsSolved.infer outerNames arms) (parameters : scheme.Parameters)
    (floatCheck : Empty → Empty → Bool) (value : Value)
    (valid : CommonPatternTyping.valueAt (scheme.instantiate parameters 0).1 value) (index : Nat) :
    PartialResult (scheme.instantiate parameters 2).1
      (ScopedCaseEvaluation.runArms floatCheck CaseDataTerms.defaultEval []
        (CaseDataTerms.guardEval []) (CaseDataTerms.bodyEval []) value index arms).result := by
  have outer := EnvironmentHolds.nil outerNames ([] : Bindings Empty)
  have safe := CommonPatternSourceArmsSolved.returned_scheme_actual_partial outerNames arms scheme returned parameters
    floatCheck (defaults []) (default_partial_sound outer) (defaults_invariant [])
    (CaseDataTerms.guardEval []) (CommonAlignedCaseEvaluation.data_guard_invariant [])
    (CaseDataTerms.bodyEval []) (body_partial_sound outer) (CommonAlignedCaseEvaluation.data_body_invariant [])
    value valid index
  have same : defaults [] = CaseDataTerms.defaultEval (F := Empty) := by
    funext preceding code
    simp [defaults, CaseDataTerms.defaultEval]
  rw [same] at safe
  exact safe

end Yulang.CommonPatternConcreteCaseSafety
