import Yulang.CommonCaseConstructorBounds
import Yulang.CommonPatternSourceProgramEnvironments

/-! A real finite solved family for source case environment premises, a
Common record input bound, and pure-witness record coverage. All returned
parameters give actual finite-data program progress. Aggregate effect rows,
presence legality and executable-default coverage are still separate. -/

namespace Yulang.CommonCaseRecordEnvironmentFamily

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration
open CommonPatternGenerationProvenance (SafeFormula SafeEnvironment)
open CommonPatternSourceArmsSolved (SourceArm)
open CommonCaseRecordReadout (Specification shapes)
open CommonPatternTyping (valueAt)

/-- Semantic pure-witness coverage. Eligibility is stated as a literal source
syntax image, without invoking the finite erasure/checker or a solver. -/
def Coverage (floatCheck : Empty → Empty → Bool) (specification : Specification) (arms : List SourceArm) : Prop :=
  ∀ fields, CommonCaseRecordCells.Domain (shapes specification) fields →
    ∃ arm ∈ arms, arm.guard = none ∧ ∃ pure : CasePatterns.Pattern Empty Empty,
      Patterns.map Empty.elim pure = arm.pattern ∧ ∃ returned,
        (ScopedCasePatterns.run floatCheck CaseDataTerms.defaultEval [] arm.pattern (.record fields)).result = .ok (some returned)

theorem coverage_exact (floatCheck : Empty → Empty → Bool) (specification : Specification) (arms : List SourceArm) :
    CommonCaseRecordSourceCoverage.check floatCheck (shapes specification) arms = true ↔ Coverage floatCheck specification arms := by
  simp only [CommonCaseRecordSourceCoverage.check_matches_exact floatCheck CaseDataTerms.defaultEval [],
    Coverage, CommonPurePatternErasure.erase_exact]

def Premises (outerNames : List Nat) (environment : List (CommonSyntax.Binding Common.model))
    (floatCheck : Empty → Empty → Bool) (specification : Specification) (program : CaseDataProgram.Program Empty)
    (subject : Comp Common.model) (guardRow : Common.Row) (result : Comp Common.model) : Prop :=
  CommonPatternSourceProgramEnvironments.Premises outerNames environment program subject guardRow result ∧
    Common.Subtype subject.1 (CommonCaseRecordReadout.type specification) ∧ Coverage floatCheck specification program.arms

def generatePremises (outerNames : List Nat) (environment : SchemeEnv α) (floatCheck : Empty → Empty → Bool)
    (specification : Specification) (program : CaseDataProgram.Program Empty) (subject : CompTerm α)
    (guardRow : RowTerm α) (result : CompTerm α) : Formula α :=
  if CommonCaseRecordSourceCoverage.check floatCheck (shapes specification) program.arms then
    .and (CommonPatternSourceProgramEnvironments.generateEnvironments outerNames environment program subject guardRow result)
      (CommonCaseConstructorBounds.generateRecord specification subject.ty)
  else .bot

theorem generatePremises_exact (outerNames : List Nat) (floatCheck : Empty → Empty → Bool)
    (specification : Specification) (program : CaseDataProgram.Program Empty)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic)
    (subject : CompTerm α) (guardRow : RowTerm α) (result : CompTerm α) :
    (generatePremises outerNames symbolic floatCheck specification program subject guardRow result).Holds Common.model ρ ↔
      Premises outerNames environment floatCheck specification program (subject.eval Common.model ρ)
        (guardRow.eval Common.model ρ) (result.eval Common.model ρ) := by
  cases checked : CommonCaseRecordSourceCoverage.check floatCheck (shapes specification) program.arms with
  | false =>
      have absent : ¬ Coverage floatCheck specification program.arms := by
        intro covered
        have accepted := (coverage_exact floatCheck specification program.arms).mpr covered
        rw [checked] at accepted
        cases accepted
      simp only [generatePremises, checked, Bool.false_eq_true, ↓reduceIte, Formula.Holds, Premises, absent, and_false]
  | true =>
      have covered := (coverage_exact floatCheck specification program.arms).mp checked
      simp only [generatePremises, checked, ↓reduceIte, Formula.Holds,
        CommonPatternSourceProgramEnvironments.generateEnvironments_exact outerNames program ρ symbolic environment semantic
          coreRelated symbolicRelated subject guardRow result,
        CommonCaseConstructorBounds.generateRecord_exact, Premises, covered, and_true]
      rfl

def principal (outerNames : List Nat) (floatCheck : Empty → Empty → Bool) (specification : Specification)
    (program : CaseDataProgram.Program Empty) : Formula (Fin 3) :=
  generatePremises outerNames [] floatCheck specification program (.var 0) (.var 1) (.var 2)

theorem principal_safe (outerNames : List Nat) (floatCheck : Empty → Empty → Bool) (specification : Specification)
    (program : CaseDataProgram.Program Empty) : SafeFormula (principal outerNames floatCheck specification program) := by
  unfold principal generatePremises
  split
  · exact .and (CommonPatternSourceProgramEnvironments.principal_safe outerNames program)
      (CommonCaseConstructorBounds.safe_generateRecord specification (.var 0) ⟨rfl, rfl, rfl⟩)
  · exact .bot

theorem principal_exact (outerNames : List Nat) (floatCheck : Empty → Empty → Bool) (specification : Specification)
    (program : CaseDataProgram.Program Empty) (ρ : Fin 3 → Comp Common.model) :
    (principal outerNames floatCheck specification program).Holds Common.model ρ ↔
      Premises outerNames [] floatCheck specification program (ρ 0) (ρ 1).2 (ρ 2) :=
  generatePremises_exact outerNames floatCheck specification program ρ [] [] [] (CommonSyntax.EnvRel.nil Common.model)
    (EnvRel.nil Common.model ρ) _ _ _

def solvePremises (outerNames : List Nat) (floatCheck : Empty → Empty → Bool) (specification : Specification)
    (program : CaseDataProgram.Program Empty) : List (CommonPatternFiniteSchemes.Scheme 3) :=
  CommonPatternFiniteSchemes.infer (principal outerNames floatCheck specification program)

theorem all_parameter_premises (outerNames : List Nat) (floatCheck : Empty → Empty → Bool) (specification : Specification)
    (program : CaseDataProgram.Program Empty) (scheme : CommonPatternFiniteSchemes.Scheme 3)
    (member : scheme ∈ solvePremises outerNames floatCheck specification program) (parameters : scheme.Parameters) :
    Premises outerNames [] floatCheck specification program (scheme.instantiate parameters 0) (scheme.instantiate parameters 1).2
      (scheme.instantiate parameters 2) :=
  (principal_exact outerNames floatCheck specification program _).mp
    (CommonPatternFiniteSchemes.all_parameter_holds _ scheme member parameters)

theorem premises_instances_exact (outerNames : List Nat) (floatCheck : Empty → Empty → Bool) (specification : Specification)
    (program : CaseDataProgram.Program Empty) (ρ : Fin 3 → Comp Common.model) :
    Premises outerNames [] floatCheck specification program (ρ 0) (ρ 1).2 (ρ 2) ↔
      ∃ scheme ∈ solvePremises outerNames floatCheck specification program, ∃ parameters : scheme.Parameters,
        CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters) ρ :=
  (principal_exact outerNames floatCheck specification program ρ).symm.trans
    (CommonPatternFiniteSchemes.formula_instances_exact _ (principal_safe outerNames floatCheck specification program) ρ)

theorem no_premises_exact (outerNames : List Nat) (floatCheck : Empty → Empty → Bool) (specification : Specification)
    (program : CaseDataProgram.Program Empty) : solvePremises outerNames floatCheck specification program = [] ↔
      ¬ ∃ ρ : Fin 3 → Comp Common.model, Premises outerNames [] floatCheck specification program (ρ 0) (ρ 1).2 (ρ 2) := by
  rw [solvePremises, CommonPatternFiniteSchemes.infer_empty_iff _ (principal_safe outerNames floatCheck specification program)]
  exact not_congr (exists_congr (principal_exact outerNames floatCheck specification program))

/-- Every returned unrestricted parameter gives real source execution and a
typed value. No environment, domain, matcher success, selected arm or residual
condition is required after instantiating a returned scheme. -/
theorem all_parameter_program_progress (outerNames : List Nat) (floatCheck : Empty → Empty → Bool) (specification : Specification)
    (program : CaseDataProgram.Program Empty) (scheme : CommonPatternFiniteSchemes.Scheme 3)
    (member : scheme ∈ solvePremises outerNames floatCheck specification program) (parameters : scheme.Parameters) :
    ∃ output, (ScopedCaseDataProgram.eval floatCheck [] program).result = .ok (some output) ∧
      valueAt (scheme.instantiate parameters 2).1 output := by
  have premises := all_parameter_premises outerNames floatCheck specification program scheme member parameters
  exact CommonCaseRecordSourceCoverage.record_program_progress (CommonPatternDataSafety.EnvironmentHolds.nil outerNames [])
    program _ premises.1.1 (fun arm member => ⟨_, premises.1.2 arm member⟩) specification premises.2.1 floatCheck
    ((coverage_exact floatCheck specification program.arms).mpr premises.2.2)

end Yulang.CommonCaseRecordEnvironmentFamily
