import Yulang.CommonPatternCorePrefixBridge
import Yulang.CommonCaseCoreBoundedSolved
import Yulang.CommonPatternCoreRuntimeEnvironment

/-! Actual finite Core families supply every static premise for all free
parameters. The explicit remaining source-prefix adequacy interface is fixed
independently of the scheme parameters. Guards decode the same value
interpreter; no separate Boolean oracle or termination premise is assumed.
This is still the row-upper-bound environment factor of full case typing. -/

namespace Yulang.CommonCaseCorePrefixSolved

open Core
open PresenceGeneration
open CommonPatternFinitePrefixes (Computation Safe ops logic)
open CommonPatternCorePrefixBridge (EvaluationSound default_sound guardOf guard_sound)
open CommonPatternSourceScope (corePrefix)
open CommonPatternTyping (valueAt bindingTypes)
open CommonCaseComputationSafety (GuardSound BodySound ResultHolds)
open CommonCaseCoreBoundedGeneration (Arm runtimeArm GuardTyped BodyTyped environment_arm_exact)
open CommonCaseCoreBoundedSolved (Premises solvePremises all_parameter_premises)
open CaseValues (Bindings BindingsHold)

theorem guards_safe (source : E → Common.Row) (failure : R → Common.Row)
    (environment : List (CommonSyntax.Binding Common.model))
    (evaluate : Bindings Empty → Required.Term → Computation E R CommonData.Value)
    (sound : EvaluationSound source failure environment evaluate) (invalid : Computation E R Bool)
    (cap : Common.Row) :
    GuardSound (logic source failure) cap (GuardTyped environment cap) (guardOf evaluate invalid) :=
  fun code types typed actual valid => guard_sound source failure environment evaluate sound invalid cap types code typed actual valid

theorem bodies_safe (source : E → Common.Row) (failure : R → Common.Row)
    (environment : List (CommonSyntax.Binding Common.model))
    (evaluate : Bindings Empty → Required.Term → Computation E R CommonData.Value)
    (sound : EvaluationSound source failure environment evaluate) (cap : Common.Row) :
    BodySound (logic source failure) cap (BodyTyped environment cap) (fun code actual => evaluate actual code) :=
  fun code types target typed actual valid => sound types code (target, cap) typed actual valid

theorem case_finite_prefixes (environment : List (CommonSyntax.Binding Common.model))
    (subject : Required.Term) (arms : List Arm) (input target : Common.Ty) (cap : Common.Row)
    (premises : Premises environment subject arms input target cap)
    (source : E → Common.Row) (failure : R → Common.Row)
    (evaluate : Bindings Empty → Required.Term → Computation E R CommonData.Value)
    (sound : EvaluationSound source failure environment evaluate) (invalid : Computation E R Bool)
    (floatCheck : Empty → Empty → Bool) :
    Safe source failure
      (CommonCaseComputations.eval (ops E R) (CommonCaseFinitePrefixes.visits E R) floatCheck evaluate []
        (guardOf evaluate invalid) (fun code actual => evaluate actual code) (evaluate [] subject) (arms.map runtimeArm))
      (ResultHolds target) cap := by
  have subjectSafe := sound [] subject (input, cap) premises.1 [] .nil
  have armTyped : ∀ arm ∈ arms.map runtimeArm, CommonCaseBoundedObservations.ArmTyping
      (CommonPatternCoreBoundedDefaults.DefaultTyped environment cap) (GuardTyped environment cap)
      (BodyTyped environment cap) [] arm input target := by
    intro arm member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact (environment_arm_exact environment original input target cap).mp (premises.2 original originalMember)
  exact CommonCaseFinitePrefixes.eval_finite_prefixes (types := []) source failure cap floatCheck evaluate
    (default_sound source failure environment evaluate sound cap) [] .nil (guardOf evaluate invalid)
    (guards_safe source failure environment evaluate sound invalid cap) (fun code actual => evaluate actual code)
    (bodies_safe source failure environment evaluate sound cap) _ subjectSafe _ armTyped

/-- No model/residual predicate is added to the returned parameters. The
sole interpreter bridge is a global source-prefix contract, not a solver
filter. Coverage and match-failure elimination are not claimed. -/
theorem all_parameter_case_prefixes (subject : Required.Term) (arms : List Arm)
    (scheme : CommonPatternFiniteSchemes.Scheme 3) (member : scheme ∈ solvePremises subject arms)
    (parameters : scheme.Parameters) (source : E → Common.Row) (failure : R → Common.Row)
    (evaluate : Bindings Empty → Required.Term → Computation E R CommonData.Value)
    (sound : EvaluationSound source failure [] evaluate) (invalid : Computation E R Bool)
    (floatCheck : Empty → Empty → Bool) :
    Safe source failure
      (CommonCaseComputations.eval (ops E R) (CommonCaseFinitePrefixes.visits E R) floatCheck evaluate []
        (guardOf evaluate invalid) (fun code actual => evaluate actual code) (evaluate [] subject) (arms.map runtimeArm))
      (ResultHolds (scheme.instantiate parameters 1).1) (scheme.instantiate parameters 2).2 :=
  case_finite_prefixes [] subject arms _ _ _ (all_parameter_premises subject arms scheme member parameters)
    source failure evaluate sound invalid floatCheck

theorem all_parameter_pattern_prefixes (pattern : CasePatterns.Pattern Empty Required.Term)
    (subject : CommonData.Value) (returned : Bindings Empty)
    (scheme : CommonPatternFiniteSchemes.Scheme 2)
    (member : scheme ∈ CommonPatternCoreRuntimeEnvironment.solveEnvironments pattern subject returned)
    (parameters : scheme.Parameters) (source : E → Common.Row) (failure : R → Common.Row)
    (evaluate : Bindings Empty → Required.Term → Computation E R CommonData.Value)
    (sound : EvaluationSound source failure [] evaluate) (floatCheck : Empty → Empty → Bool) :
    ∃ bindings,
      CommonAlignedPatternTyping.Typing (CommonPatternCoreBoundedDefaults.DefaultTyped [] (scheme.instantiate parameters 1).2)
        [] pattern (scheme.instantiate parameters 0).1 bindings ∧
      Safe source failure (CommonPatternComputations.run (ops E R) floatCheck evaluate [] pattern subject)
        (CommonPatternComputationSafety.OptionHolds bindings) (scheme.instantiate parameters 1).2 := by
  obtain ⟨names, bindings, typed, subjectTyped, returnedTyped⟩ :=
    CommonPatternCoreRuntimeEnvironment.all_parameter_witness pattern subject returned scheme member parameters
  exact ⟨bindings, typed, CommonPatternFinitePrefixes.typing_finite_prefixes source failure _ floatCheck evaluate
    (default_sound source failure [] evaluate sound _) typed [] .nil subject subjectTyped⟩

end Yulang.CommonCaseCorePrefixSolved
