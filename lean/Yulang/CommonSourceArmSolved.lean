import Yulang.CommonPatternSourceArmSolved
import Yulang.CommonSourceArmGeneration
import Yulang.CommonSourcePatternGenerationProvenance
import Yulang.CommonPatternFormulaEquivalence

/-! Actual source arm-environment constraints consume the finite solved
boundary. All syntax invariants are proved from generation. This is the
arm-environment factor of B2, not aggregate effects or full case inference. -/

namespace Yulang.CommonSourceArmSolved

set_option backward.isDefEq.respectTransparency false

open Core.PresenceGeneration
open CommonPatternEnvironment
open CommonPatternGenerationProvenance
open CommonPatternAllocation (ambient bindingSlots)
open CommonPatternSourceScope (generateData)
open CommonSourceArmGeneration (generateEnvironments EnvironmentTyping)
open CommonPatternSourceArmGeneration (consumer generateGuard)
open CasePatterns (Pattern)

open CommonPatternSourceArmSolved (safe_consumer)

theorem safe_generateEnvironments (outerNames : List Nat) (environment : SchemeEnv α)
    (good : SafeEnvironment environment) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (guard : Option (CaseDataTerms.Expr Empty)) (body : CaseDataTerms.Expr Empty)
    (input : TyTerm α) (inputGood : Input input)
    (guardRow : RowTerm α) (guardGood : PresenceSourceConstraintSupport.simpleRow guardRow = true)
    (result : CompTerm α) (typeGood : BinderType result.ty)
    (rowGood : PresenceSourceConstraintSupport.simpleRow result.row = true) :
    SafeFormula (generateEnvironments outerNames environment pattern guard body input guardRow result) := by
  unfold generateEnvironments
  split
  · apply safe_close
    exact .and
      (CommonSourcePatternGenerationProvenance.safe_constraints _ environment good []
        (by intro binding member; cases member) input inputGood)
      (safe_consumer _ environment good outerNames guard body guardRow guardGood result typeGood rowGood)
  · exact .bot

def principal (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (guard : Option (CaseDataTerms.Expr Empty)) (body : CaseDataTerms.Expr Empty) : Formula (Fin 3) :=
  generateEnvironments outerNames [] pattern guard body (.var 0) (.var 1) (.var 2)

theorem principal_safe (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (guard : Option (CaseDataTerms.Expr Empty)) (body : CaseDataTerms.Expr Empty) :
    SafeFormula (principal outerNames pattern guard body) := by
  have good : SafeEnvironment ([] : SchemeEnv (Fin 3)) := by
    constructor <;> intro scheme member <;> cases member
  exact safe_generateEnvironments outerNames [] good pattern guard body _ ⟨rfl, rfl, rfl⟩ _ rfl _ ⟨rfl, rfl⟩ rfl

theorem principal_exact (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (guard : Option (CaseDataTerms.Expr Empty)) (body : CaseDataTerms.Expr Empty)
    (assignment : Fin 3 → Comp Common.model) :
    (principal outerNames pattern guard body).Holds Common.model assignment ↔
      EnvironmentTyping outerNames [] pattern guard body (assignment 0).1 (assignment 1).2 (assignment 2) :=
  CommonSourceArmGeneration.generateEnvironments_exact pattern outerNames assignment [] [] []
    (Core.CommonSyntax.EnvRel.nil Common.model) (EnvRel.nil Common.model assignment) guard body _ _ _

def infer (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (guard : Option (CaseDataTerms.Expr Empty)) (body : CaseDataTerms.Expr Empty) :
    List (CommonPatternFiniteSchemes.Scheme 3) :=
  CommonPatternFiniteSchemes.infer (principal outerNames pattern guard body)

/-- Every actual returned scheme at every unrestricted row/type/recursive
parameter product supplies the independent source arm environments. -/
theorem all_parameter_environments (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (guard : Option (CaseDataTerms.Expr Empty)) (body : CaseDataTerms.Expr Empty)
    (scheme : CommonPatternFiniteSchemes.Scheme 3) (returned : scheme ∈ infer outerNames pattern guard body)
    (parameters : scheme.Parameters) :
    EnvironmentTyping outerNames [] pattern guard body (scheme.instantiate parameters 0).1
      (scheme.instantiate parameters 1).2 (scheme.instantiate parameters 2) :=
  (principal_exact outerNames pattern guard body _).mp
    (CommonPatternFiniteSchemes.all_parameter_holds _ scheme returned parameters)

/-- The source generator supplies every finite syntax certificate internally.
No residual or support predicate appears in the scheme parameter domain. -/
theorem environments_instances_exact (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (guard : Option (CaseDataTerms.Expr Empty)) (body : CaseDataTerms.Expr Empty)
    (assignment : Fin 3 → Comp Common.model) :
    EnvironmentTyping outerNames [] pattern guard body (assignment 0).1 (assignment 1).2 (assignment 2) ↔
      ∃ scheme ∈ infer outerNames pattern guard body, ∃ parameters : scheme.Parameters,
        CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters) assignment :=
  (principal_exact outerNames pattern guard body assignment).symm.trans
    (CommonPatternFiniteSchemes.formula_instances_exact _ (principal_safe outerNames pattern guard body) assignment)

theorem environments_rejected_exact (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (guard : Option (CaseDataTerms.Expr Empty)) (body : CaseDataTerms.Expr Empty) :
    infer outerNames pattern guard body = [] ↔
      ¬ ∃ assignment : Fin 3 → Comp Common.model,
        EnvironmentTyping outerNames [] pattern guard body (assignment 0).1 (assignment 1).2 (assignment 2) := by
  rw [infer, CommonPatternFiniteSchemes.infer_empty_iff _ (principal_safe outerNames pattern guard body)]
  exact not_congr (exists_congr (principal_exact outerNames pattern guard body))

end Yulang.CommonSourceArmSolved
