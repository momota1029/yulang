import Yulang.CommonCaseCoreBoundedGeneration

/-! One finite Core family retains the subject/default/guard/body row cap.
Its exact independent premises remain an upper-bound factor of full B2.
The operational conclusions explicitly require the unresolved interpreter
contracts and use canonical matching for already indexed Core terms. -/

namespace Yulang.CommonCaseCoreBoundedSolved

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration
open CommonPatternEnvironment
open CommonPatternGenerationProvenance (SafeEnvironment SafeFormula)
open CommonPatternSourceScope (corePrefix)
open CommonPatternTyping (valueAt bindingTypes)
open CommonCaseCoreEnvironments (generateTerm generateTerm_exact)
open CommonCaseCoreBoundedGeneration
open CommonPatternCoreBoundedSolved (EvaluationSound default_observations)
open CommonCaseBoundedObservations (GuardObservationSound BodyObservationSound)
open CommonCaseEffectPaths (observationRow)
open EvaluationTrace (Logged)
open CaseEvaluation (Event)

def Premises (environment : List (CommonSyntax.Binding Common.model)) (subject : Required.Term)
    (arms : List Arm) (input target : Common.Ty) (cap : Common.Row) : Prop :=
  CommonSyntax.Typing Common.model environment subject (input, cap) ∧
    ∀ arm ∈ arms, EnvironmentTyping environment arm.1 arm.2.1 arm.2.2 input target cap

def generatePremises (environment : SchemeEnv α) (subject : Required.Term) (arms : List Arm)
    (input target : TyTerm α) (cap : RowTerm α) : Formula α :=
  .and (generateTerm environment subject ⟨input, cap⟩) (generateAll environment input target cap arms)

theorem generatePremises_exact (subject : Required.Term) (arms : List Arm)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic) (input target : TyTerm α) (cap : RowTerm α) :
    (generatePremises symbolic subject arms input target cap).Holds Common.model ρ ↔
      Premises environment subject arms (input.eval Common.model ρ) (target.eval Common.model ρ) (cap.eval Common.model ρ) :=
  and_congr (generateTerm_exact subject ρ symbolic environment semantic coreRelated symbolicRelated _)
    (generateAll_exact arms ρ symbolic environment semantic coreRelated symbolicRelated input target cap)

def principal (subject : Required.Term) (arms : List Arm) : Formula (Fin 3) :=
  generatePremises [] subject arms (.var 0) (.var 1) (.var 2)

theorem principal_safe (subject : Required.Term) (arms : List Arm) : SafeFormula (principal subject arms) := by
  have good : SafeEnvironment ([] : SchemeEnv (Fin 3)) := by
    constructor <;> intro scheme member <;> cases member
  exact .and (CommonCaseCoreSolvedEnvironments.safe_generateTerm [] good subject _ ⟨rfl, rfl⟩ rfl)
    (safe_generateAll arms [] good _ ⟨rfl, rfl, rfl⟩ _ ⟨rfl, rfl⟩ _ rfl)

theorem principal_exact (subject : Required.Term) (arms : List Arm) (ρ : Fin 3 → Comp Common.model) :
    (principal subject arms).Holds Common.model ρ ↔ Premises [] subject arms (ρ 0).1 (ρ 1).1 (ρ 2).2 :=
  generatePremises_exact subject arms ρ [] [] [] (CommonSyntax.EnvRel.nil Common.model) (EnvRel.nil Common.model ρ) _ _ _

def solvePremises (subject : Required.Term) (arms : List Arm) : List (CommonPatternFiniteSchemes.Scheme 3) :=
  CommonPatternFiniteSchemes.infer (principal subject arms)

theorem all_parameter_premises (subject : Required.Term) (arms : List Arm)
    (scheme : CommonPatternFiniteSchemes.Scheme 3) (member : scheme ∈ solvePremises subject arms)
    (parameters : scheme.Parameters) :
    Premises [] subject arms (scheme.instantiate parameters 0).1 (scheme.instantiate parameters 1).1
      (scheme.instantiate parameters 2).2 :=
  (principal_exact subject arms _).mp (CommonPatternFiniteSchemes.all_parameter_holds _ scheme member parameters)

theorem premises_instances_exact (subject : Required.Term) (arms : List Arm) (ρ : Fin 3 → Comp Common.model) :
    Premises [] subject arms (ρ 0).1 (ρ 1).1 (ρ 2).2 ↔
      ∃ scheme ∈ solvePremises subject arms, ∃ parameters : scheme.Parameters,
        CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters) ρ :=
  (principal_exact subject arms ρ).symm.trans
    (CommonPatternFiniteSchemes.formula_instances_exact _ (principal_safe subject arms) ρ)

theorem no_premises_exact (subject : Required.Term) (arms : List Arm) : solvePremises subject arms = [] ↔
    ¬ ∃ ρ : Fin 3 → Comp Common.model, Premises [] subject arms (ρ 0).1 (ρ 1).1 (ρ 2).2 := by
  rw [solvePremises, CommonPatternFiniteSchemes.infer_empty_iff _ (principal_safe subject arms)]
  exact not_congr (exists_congr (principal_exact subject arms))

/-- The Bool-valued guard interpreter's separate observation interface.
Its connection to general Core execution and Bool readout remains unproved. -/
def GuardEvaluationSound (source : E → Common.Row) (failure : R → Common.Row)
    (environment : List (CommonSyntax.Binding Common.model))
    (evaluate : Required.Term → CaseValues.Bindings Empty → Logged (Event E) R Bool) : Prop :=
  ∀ types code row, CommonSyntax.Typing Common.model (corePrefix types ++ environment) code (.base .bool, row) →
    ∀ actual, CaseValues.BindingsHold (bindingTypes types) actual →
      Common.rowLe (observationRow source failure (evaluate code actual)) row

theorem guards_bounded (source : E → Common.Row) (failure : R → Common.Row)
    (environment : List (CommonSyntax.Binding Common.model))
    (evaluate : Required.Term → CaseValues.Bindings Empty → Logged (Event E) R Bool)
    (sound : GuardEvaluationSound source failure environment evaluate) (cap : Common.Row) :
    GuardObservationSound source failure cap (GuardTyped environment cap) evaluate :=
  fun code types typed actual valid => sound types code cap typed actual valid

theorem bodies_bounded (source : E → Common.Row) (failure : R → Common.Row)
    (environment : List (CommonSyntax.Binding Common.model))
    (evaluate : CaseValues.Bindings Empty → Required.Term → Logged (Event E) R CommonData.Value)
    (sound : EvaluationSound source failure environment evaluate) (cap : Common.Row) :
    BodyObservationSound source failure cap (BodyTyped environment cap) (fun code actual => evaluate actual code) :=
  fun code types target typed actual valid => sound types code (target, cap) typed actual valid

theorem canonical_case_partial_and_bound (environment : List (CommonSyntax.Binding Common.model))
    (subject : Required.Term) (arms : List Arm) (input target : Common.Ty) (cap : Common.Row)
    (premises : Premises environment subject arms input target cap)
    (source : E → Common.Row) (failure : R → Common.Row)
    (evaluate : CaseValues.Bindings Empty → Required.Term → Logged (Event E) R CommonData.Value)
    (sound : EvaluationSound source failure environment evaluate)
    (guardEval : Required.Term → CaseValues.Bindings Empty → Logged (Event E) R Bool)
    (guards : GuardEvaluationSound source failure environment guardEval) (floatCheck : Empty → Empty → Bool) :
    CommonPatternSourceCasePartial.PartialResult target
      (CommonAlignedCaseEvaluation.eval floatCheck evaluate [] guardEval (fun code actual => evaluate actual code)
        (evaluate [] subject) (arms.map runtimeArm)).result ∧
      Common.rowLe (observationRow source failure
        (CommonAlignedCaseEvaluation.eval floatCheck evaluate [] guardEval (fun code actual => evaluate actual code)
          (evaluate [] subject) (arms.map runtimeArm))) cap := by
  have subjectSafe := sound [] subject (input, cap) premises.1 [] .nil
  have armTyped : ∀ arm ∈ arms.map runtimeArm, CommonCaseBoundedObservations.ArmTyping
      (CommonPatternCoreBoundedDefaults.DefaultTyped environment cap) (GuardTyped environment cap)
      (BodyTyped environment cap) [] arm input target := by
    intro arm member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact (environment_arm_exact environment original input target cap).mp (premises.2 original originalMember)
  exact CommonCaseBoundedObservations.eval_partial_and_bound (types := []) source failure cap floatCheck evaluate
    (default_observations source failure environment evaluate sound cap) [] .nil guardEval
    (guards_bounded source failure environment guardEval guards cap) (fun code actual => evaluate actual code)
    (bodies_bounded source failure environment evaluate sound cap) _ armTyped _ subjectSafe.1 subjectSafe.2

theorem all_parameter_canonical_case_bound (subject : Required.Term) (arms : List Arm)
    (scheme : CommonPatternFiniteSchemes.Scheme 3) (member : scheme ∈ solvePremises subject arms)
    (parameters : scheme.Parameters) (source : E → Common.Row) (failure : R → Common.Row)
    (evaluate : CaseValues.Bindings Empty → Required.Term → Logged (Event E) R CommonData.Value)
    (sound : EvaluationSound source failure [] evaluate)
    (guardEval : Required.Term → CaseValues.Bindings Empty → Logged (Event E) R Bool)
    (guards : GuardEvaluationSound source failure [] guardEval) (floatCheck : Empty → Empty → Bool) :
    CommonPatternSourceCasePartial.PartialResult (scheme.instantiate parameters 1).1
      (CommonAlignedCaseEvaluation.eval floatCheck evaluate [] guardEval (fun code actual => evaluate actual code)
        (evaluate [] subject) (arms.map runtimeArm)).result ∧
      Common.rowLe (observationRow source failure
        (CommonAlignedCaseEvaluation.eval floatCheck evaluate [] guardEval (fun code actual => evaluate actual code)
          (evaluate [] subject) (arms.map runtimeArm))) (scheme.instantiate parameters 2).2 :=
  canonical_case_partial_and_bound [] subject arms _ _ _ (all_parameter_premises subject arms scheme member parameters)
    source failure evaluate sound guardEval guards floatCheck

end Yulang.CommonCaseCoreBoundedSolved
