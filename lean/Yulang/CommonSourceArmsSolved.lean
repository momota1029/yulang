import Yulang.CommonSourceArmSolved
import Yulang.CommonSourceCasePartial

/-! The environment factor for every finite source arm list, using shared
ambient subject/guard/result slots and independent per-arm binder allocation.
This is static conjunction, not eager execution of the arms. -/

namespace Yulang.CommonSourceArmsSolved

set_option backward.isDefEq.respectTransparency false

open Core.PresenceGeneration
open CommonPatternGenerationProvenance (SafeEnvironment SafeFormula Input BinderType)
open CommonSourceArmGeneration (EnvironmentTyping generateEnvironments)
open CommonSourceArmSolved (safe_generateEnvironments)
open CommonSourceCasePartial (BodyPartialSound PartialResult)
open CommonPatternSourceElaboration (DefaultTyped)
open CaseValues EvaluationTrace
open CaseEvaluation (Arm Event)

abbrev SourceArm := Arm Empty (CaseDataTerms.Expr Empty) (CaseDataTerms.Expr Empty) (CaseDataTerms.Expr Empty)

def generateAll (outerNames : List Nat) (environment : SchemeEnv α)
    (input : TyTerm α) (guardRow : RowTerm α) (result : CompTerm α) : List SourceArm → Formula α
  | [] => .top
  | arm :: rest => .and (generateEnvironments outerNames environment arm.pattern arm.guard arm.body input guardRow result)
      (generateAll outerNames environment input guardRow result rest)

theorem generateAll_exact (outerNames : List Nat) (arms : List SourceArm)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (Core.CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : Core.CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic)
    (input : TyTerm α) (guardRow : RowTerm α) (result : CompTerm α) :
    (generateAll outerNames symbolic input guardRow result arms).Holds Common.model ρ ↔
      ∀ arm ∈ arms, EnvironmentTyping outerNames environment arm.pattern arm.guard arm.body
        (input.eval Common.model ρ) (guardRow.eval Common.model ρ) (result.eval Common.model ρ) := by
  induction arms with
  | nil => simp [generateAll, Formula.Holds]
  | cons arm rest ih =>
      simp only [generateAll, Formula.Holds,
        CommonSourceArmGeneration.generateEnvironments_exact _ outerNames ρ symbolic environment semantic
          coreRelated symbolicRelated, ih, List.forall_mem_cons]

theorem safe_generateAll (outerNames : List Nat) (arms : List SourceArm)
    (environment : SchemeEnv α) (good : SafeEnvironment environment)
    (input : TyTerm α) (inputGood : Input input)
    (guardRow : RowTerm α) (guardGood : PresenceSourceConstraintSupport.simpleRow guardRow = true)
    (result : CompTerm α) (typeGood : BinderType result.ty)
    (rowGood : PresenceSourceConstraintSupport.simpleRow result.row = true) :
    SafeFormula (generateAll outerNames environment input guardRow result arms) := by
  induction arms with
  | nil => exact .top
  | cons arm rest ih =>
      exact .and (safe_generateEnvironments outerNames environment good arm.pattern arm.guard arm.body input inputGood
        guardRow guardGood result typeGood rowGood) ih

def principal (outerNames : List Nat) (arms : List SourceArm) : Formula (Fin 3) :=
  generateAll outerNames [] (.var 0) (.var 1) (.var 2) arms

theorem principal_safe (outerNames : List Nat) (arms : List SourceArm) : SafeFormula (principal outerNames arms) := by
  have good : SafeEnvironment ([] : SchemeEnv (Fin 3)) := by
    constructor <;> intro scheme member <;> cases member
  exact safe_generateAll outerNames arms [] good _ ⟨rfl, rfl, rfl⟩ _ rfl _ ⟨rfl, rfl⟩ rfl

theorem principal_exact (outerNames : List Nat) (arms : List SourceArm) (assignment : Fin 3 → Comp Common.model) :
    (principal outerNames arms).Holds Common.model assignment ↔
      ∀ arm ∈ arms, EnvironmentTyping outerNames [] arm.pattern arm.guard arm.body
        (assignment 0).1 (assignment 1).2 (assignment 2) :=
  generateAll_exact outerNames arms assignment [] [] [] (Core.CommonSyntax.EnvRel.nil Common.model)
    (EnvRel.nil Common.model assignment) _ _ _

def infer (outerNames : List Nat) (arms : List SourceArm) : List (CommonPatternFiniteSchemes.Scheme 3) :=
  CommonPatternFiniteSchemes.infer (principal outerNames arms)

theorem all_parameter_environments (outerNames : List Nat) (arms : List SourceArm)
    (scheme : CommonPatternFiniteSchemes.Scheme 3) (returned : scheme ∈ infer outerNames arms)
    (parameters : scheme.Parameters) :
    ∀ arm ∈ arms, EnvironmentTyping outerNames [] arm.pattern arm.guard arm.body
      (scheme.instantiate parameters 0).1 (scheme.instantiate parameters 1).2 (scheme.instantiate parameters 2) :=
  (principal_exact outerNames arms _).mp (CommonPatternFiniteSchemes.all_parameter_holds _ scheme returned parameters)

theorem environments_instances_exact (outerNames : List Nat) (arms : List SourceArm)
    (assignment : Fin 3 → Comp Common.model) :
    (∀ arm ∈ arms, EnvironmentTyping outerNames [] arm.pattern arm.guard arm.body
        (assignment 0).1 (assignment 1).2 (assignment 2)) ↔
      ∃ scheme ∈ infer outerNames arms, ∃ parameters : scheme.Parameters,
        CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters) assignment :=
  (principal_exact outerNames arms assignment).symm.trans
    (CommonPatternFiniteSchemes.formula_instances_exact _ (principal_safe outerNames arms) assignment)

theorem environments_rejected_exact (outerNames : List Nat) (arms : List SourceArm) :
    infer outerNames arms = [] ↔
      ¬ ∃ assignment : Fin 3 → Comp Common.model,
        ∀ arm ∈ arms, EnvironmentTyping outerNames [] arm.pattern arm.guard arm.body
          (assignment 0).1 (assignment 1).2 (assignment 2) := by
  rw [infer, CommonPatternFiniteSchemes.infer_empty_iff _ (principal_safe outerNames arms)]
  exact not_congr (exists_congr (principal_exact outerNames arms))

/-- The real generated solved list reaches actual first-match execution for
all parameter products. The explicit remaining contracts concern source
leaf successful returns and name dependence, not successful case execution. -/
theorem returned_scheme_actual_partial (outerNames : List Nat) (arms : List SourceArm)
    (scheme : CommonPatternFiniteSchemes.Scheme 3) (returned : scheme ∈ infer outerNames arms)
    (parameters : scheme.Parameters) (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → CaseDataTerms.Expr Empty → Logged (Event E) R (Value Empty))
    (defaults : CommonPatternPartialSafety.DefaultPartialSound (DefaultTyped outerNames []) defaultEval)
    (defaultNames : CommonPatternAlignedMatcher.DefaultInvariant defaultEval)
    (guardEval : CaseDataTerms.Expr Empty → Bindings Empty → Logged (Event E) R Bool)
    (guardNames : CommonAlignedCaseEvaluation.NamedInvariant guardEval)
    (bodyEval : CaseDataTerms.Expr Empty → Bindings Empty → Logged (Event E) R (Value Empty))
    (bodies : BodyPartialSound outerNames [] bodyEval)
    (bodyNames : CommonAlignedCaseEvaluation.NamedInvariant bodyEval)
    (value : Value Empty) (valid : CommonPatternTyping.valueAt (scheme.instantiate parameters 0).1 value)
    (index : Nat) :
    PartialResult (scheme.instantiate parameters 2).1
      (ScopedCaseEvaluation.runArms floatCheck defaultEval [] guardEval bodyEval value index arms).result :=
  CommonSourceCasePartial.actual_runArms_partial floatCheck defaultEval defaults defaultNames
    guardEval guardNames bodyEval bodies bodyNames arms
    (fun arm member => ⟨_, all_parameter_environments outerNames arms scheme returned parameters arm member⟩)
    value valid index

end Yulang.CommonSourceArmsSolved
