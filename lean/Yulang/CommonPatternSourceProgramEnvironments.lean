import Yulang.CommonPatternConcreteCaseTotal

/-! Source subject and arm-environment premises in one real finite family.
These are explicitly factors of full case typing: aggregate operation rows,
source presence legality and exhaustiveness have not been added to them. -/

namespace Yulang.CommonPatternSourceProgramEnvironments

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration
open CommonPatternGenerationProvenance (SafeEnvironment SafeFormula)
open CommonPatternSourceArmGeneration (EnvironmentTyping)
open CommonPatternSourceScope (generateData generateData_exact)

def Premises (outerNames : List Nat) (environment : List (CommonSyntax.Binding Common.model))
    (program : CaseDataProgram.Program Empty) (subject : Comp Common.model)
    (guardRow : Common.Row) (result : Comp Common.model) : Prop :=
  CommonSyntax.Typing Common.model environment (Data.embed outerNames program.scrutinee) subject ∧
    ∀ arm ∈ program.arms,
      EnvironmentTyping outerNames environment arm.pattern arm.guard arm.body subject.1 guardRow result

def generateEnvironments (outerNames : List Nat) (environment : SchemeEnv α)
    (program : CaseDataProgram.Program Empty) (subject : CompTerm α) (guardRow : RowTerm α)
    (result : CompTerm α) : Formula α :=
  .and (generateData environment outerNames program.scrutinee subject)
    (CommonPatternSourceArmsSolved.generateAll outerNames environment subject.ty guardRow result program.arms)

theorem generateEnvironments_exact (outerNames : List Nat) (program : CaseDataProgram.Program Empty)
    (assignment : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model assignment symbolic semantic)
    (subject : CompTerm α) (guardRow : RowTerm α) (result : CompTerm α) :
    (generateEnvironments outerNames symbolic program subject guardRow result).Holds Common.model assignment ↔
      Premises outerNames environment program (subject.eval Common.model assignment)
        (guardRow.eval Common.model assignment) (result.eval Common.model assignment) := by
  exact and_congr (generateData_exact program.scrutinee outerNames assignment symbolic environment semantic
    coreRelated symbolicRelated subject)
    (CommonPatternSourceArmsSolved.generateAll_exact outerNames program.arms assignment symbolic environment semantic
      coreRelated symbolicRelated subject.ty guardRow result)

def principal (outerNames : List Nat) (program : CaseDataProgram.Program Empty) : Formula (Fin 3) :=
  generateEnvironments outerNames [] program (.var 0) (.var 1) (.var 2)

theorem principal_safe (outerNames : List Nat) (program : CaseDataProgram.Program Empty) :
    SafeFormula (principal outerNames program) := by
  have good : SafeEnvironment ([] : SchemeEnv (Fin 3)) := by
    constructor <;> intro scheme member <;> cases member
  exact .and (CommonPatternSourceArmSolved.safe_generateData [] good outerNames program.scrutinee _ ⟨rfl, rfl⟩ rfl)
    (CommonPatternSourceArmsSolved.safe_generateAll outerNames program.arms [] good _ ⟨rfl, rfl, rfl⟩ _ rfl _ ⟨rfl, rfl⟩ rfl)

theorem principal_exact (outerNames : List Nat) (program : CaseDataProgram.Program Empty)
    (assignment : Fin 3 → Comp Common.model) :
    (principal outerNames program).Holds Common.model assignment ↔
      Premises outerNames [] program (assignment 0) (assignment 1).2 (assignment 2) :=
  generateEnvironments_exact outerNames program assignment [] [] [] (CommonSyntax.EnvRel.nil Common.model)
    (EnvRel.nil Common.model assignment) _ _ _

def solveEnvironments (outerNames : List Nat) (program : CaseDataProgram.Program Empty) :
    List (CommonPatternFiniteSchemes.Scheme 3) := CommonPatternFiniteSchemes.infer (principal outerNames program)

theorem all_parameter_premises (outerNames : List Nat) (program : CaseDataProgram.Program Empty)
    (scheme : CommonPatternFiniteSchemes.Scheme 3) (returned : scheme ∈ solveEnvironments outerNames program)
    (parameters : scheme.Parameters) :
    Premises outerNames [] program (scheme.instantiate parameters 0) (scheme.instantiate parameters 1).2
      (scheme.instantiate parameters 2) :=
  (principal_exact outerNames program _).mp (CommonPatternFiniteSchemes.all_parameter_holds _ scheme returned parameters)

theorem premises_instances_exact (outerNames : List Nat) (program : CaseDataProgram.Program Empty)
    (assignment : Fin 3 → Comp Common.model) :
    Premises outerNames [] program (assignment 0) (assignment 1).2 (assignment 2) ↔
      ∃ scheme ∈ solveEnvironments outerNames program, ∃ parameters : scheme.Parameters,
        CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters) assignment :=
  (principal_exact outerNames program assignment).symm.trans
    (CommonPatternFiniteSchemes.formula_instances_exact _ (principal_safe outerNames program) assignment)

theorem no_environment_solution_exact (outerNames : List Nat) (program : CaseDataProgram.Program Empty) :
    solveEnvironments outerNames program = [] ↔
      ¬ ∃ assignment : Fin 3 → Comp Common.model,
        Premises outerNames [] program (assignment 0) (assignment 1).2 (assignment 2) := by
  rw [solveEnvironments, CommonPatternFiniteSchemes.infer_empty_iff _ (principal_safe outerNames program)]
  exact not_congr (exists_congr (principal_exact outerNames program))

/-- The real source subject is generated in the same finite family. Every
returned parameter gives safety of the actual program evaluator. Unmatched
results remain admitted because coverage is a separate factor. -/
theorem returned_program_safe (outerNames : List Nat) (program : CaseDataProgram.Program Empty)
    (scheme : CommonPatternFiniteSchemes.Scheme 3) (returned : scheme ∈ solveEnvironments outerNames program)
    (parameters : scheme.Parameters) (floatCheck : Empty → Empty → Bool) :
    CaseEvaluation.ResultHolds (CommonPatternTyping.valueAt (scheme.instantiate parameters 2).1)
      (ScopedCaseDataProgram.eval floatCheck [] program).result := by
  have premises := all_parameter_premises outerNames program scheme returned parameters
  exact CommonPatternConcreteCaseTotal.program_safe (CommonPatternDataSafety.EnvironmentHolds.nil outerNames [])
    program _ premises.1 (fun arm member => ⟨_, premises.2 arm member⟩) floatCheck

end Yulang.CommonPatternSourceProgramEnvironments
