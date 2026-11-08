import Yulang.CommonCasePrefixCoverage
import Yulang.CommonCaseCorePrefixSolved

/-! One actual finite Core family combines shared arm environments, row
bounds, a generated record input bound, and the existing pure/default
coverage certificate. Every unrestricted parameter has typed selected
successful prefixes, with no completed all-arm mismatch. The explicit
global source-prefix adequacy contract remains separate. This does not
choose the pending source presence or principal case-row policy. -/

namespace Yulang.CommonCaseCoreRecordPrefixSolved

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration
open CommonCaseCoreBoundedGeneration (Arm runtimeArm)
open CommonCaseRecordReadout (Specification shapes)
open CommonPatternFinitePrefixes (Computation Safe ops)
open CommonPatternCorePrefixBridge (EvaluationSound guardOf)
open CommonPatternGenerationProvenance (SafeFormula)
open CommonCasePrefixCoverage (SuccessfulResult)

/-- A semantic pure witness is a literal source image and is accepted on
each real record. No finite coverage checker or constraint solver occurs in
this proposition. The other disjunct is the existing independent certificate. -/
def PureCoverage (floatCheck : Empty → Empty → Bool) (specification : Specification) (arms : List Arm) : Prop :=
  ∀ fields, CommonCaseRecordCells.Domain (shapes specification) fields →
    ∃ arm ∈ arms, arm.2.1 = none ∧ ∃ pure : CasePatterns.Pattern Empty Empty,
      Patterns.map Empty.elim pure = arm.1 ∧
        CommonCaseRecordMatching.accepts floatCheck pure (.record fields) = true

def Coverage (floatCheck : Empty → Empty → Bool) (specification : Specification) (arms : List Arm) : Prop :=
  PureCoverage floatCheck specification arms ∨
    ∃ arm ∈ arms, arm.2.1 = none ∧ CommonRecordNoMiss.Total (shapes specification) arm.1

theorem pure_coverage_exact (floatCheck : Empty → Empty → Bool) (specification : Specification) (arms : List Arm) :
    CommonCaseRecordSourceCoverage.check floatCheck (shapes specification) (arms.map runtimeArm) = true ↔
      PureCoverage floatCheck specification arms := by
  rw [CommonCaseRecordSourceCoverage.check, CommonCaseRecordCoverage.check_exact]
  constructor
  · intro covered fields valid
    obtain ⟨pureArm, member, unguarded, accepted⟩ := covered fields valid
    obtain ⟨original, included, pattern, erased, rfl⟩ :=
      (CommonCaseRecordSourceCoverage.mem_pureArms (arms.map runtimeArm) pureArm).mp member
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp included
    exact ⟨source, sourceMember, unguarded, pattern,
      (CommonPurePatternErasure.erase_exact _ pattern).mp erased, accepted⟩
  · intro covered fields valid
    obtain ⟨original, included, unguarded, pattern, syntaxEq, accepted⟩ := covered fields valid
    refine ⟨⟨pattern, original.2.1, original.2.2⟩, ?_, unguarded, accepted⟩
    apply (CommonCaseRecordSourceCoverage.mem_pureArms (arms.map runtimeArm) _).mpr
    exact ⟨runtimeArm original, List.mem_map.mpr ⟨original, included, rfl⟩, pattern,
      (CommonPurePatternErasure.erase_exact _ pattern).mpr syntaxEq, rfl⟩

theorem coverage_exact (floatCheck : Empty → Empty → Bool) (specification : Specification) (arms : List Arm) :
    CommonCaseRecordDefaultCoverage.check floatCheck (shapes specification) (arms.map runtimeArm) = true ↔
      Coverage floatCheck specification arms := by
  rw [CommonCaseRecordDefaultCoverage.check_exact]
  apply or_congr (pure_coverage_exact floatCheck specification arms)
  constructor
  · rintro ⟨arm, member, unguarded, total⟩
    obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
    exact ⟨original, included, unguarded, total⟩
  · rintro ⟨arm, member, unguarded, total⟩
    exact ⟨runtimeArm arm, List.mem_map.mpr ⟨arm, member, rfl⟩, unguarded, total⟩

def Premises (environment : List (CommonSyntax.Binding Common.model))
    (floatCheck : Empty → Empty → Bool) (specification : Specification)
    (subject : Required.Term) (arms : List Arm) (input target : Common.Ty) (cap : Common.Row) : Prop :=
  CommonCaseCoreBoundedSolved.Premises environment subject arms input target cap ∧
    Common.Subtype input (CommonCaseRecordReadout.type specification) ∧ Coverage floatCheck specification arms

def generatePremises (environment : SchemeEnv α) (floatCheck : Empty → Empty → Bool)
    (specification : Specification) (subject : Required.Term) (arms : List Arm)
    (input target : TyTerm α) (cap : RowTerm α) : Formula α :=
  if CommonCaseRecordDefaultCoverage.check floatCheck (shapes specification) (arms.map runtimeArm) then
    .and (CommonCaseCoreBoundedSolved.generatePremises environment subject arms input target cap)
      (CommonCaseConstructorBounds.generateRecord specification input)
  else .bot

/-- Exact finite generation of the stated independent environment/coverage
factor, with every captured environment and every assigned slot quantified. -/
theorem generatePremises_exact (floatCheck : Empty → Empty → Bool) (specification : Specification)
    (subject : Required.Term) (arms : List Arm) (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic)
    (input target : TyTerm α) (cap : RowTerm α) :
    (generatePremises symbolic floatCheck specification subject arms input target cap).Holds Common.model ρ ↔
      Premises environment floatCheck specification subject arms (input.eval Common.model ρ)
        (target.eval Common.model ρ) (cap.eval Common.model ρ) := by
  cases checked : CommonCaseRecordDefaultCoverage.check floatCheck (shapes specification) (arms.map runtimeArm) with
  | false =>
      have absent : ¬ Coverage floatCheck specification arms := by
        intro covered
        have accepted := (coverage_exact floatCheck specification arms).mpr covered
        rw [checked] at accepted
        cases accepted
      simp only [generatePremises, checked, Bool.false_eq_true, ↓reduceIte, Formula.Holds, Premises, absent, and_false]
  | true =>
      have covered := (coverage_exact floatCheck specification arms).mp checked
      simp only [generatePremises, checked, ↓reduceIte, Formula.Holds,
        CommonCaseCoreBoundedSolved.generatePremises_exact subject arms ρ symbolic environment semantic
          coreRelated symbolicRelated input target cap,
        CommonCaseConstructorBounds.generateRecord_exact, Premises, covered, and_true]

def principal (floatCheck : Empty → Empty → Bool) (specification : Specification)
    (subject : Required.Term) (arms : List Arm) : Formula (Fin 3) :=
  generatePremises [] floatCheck specification subject arms (.var 0) (.var 1) (.var 2)

theorem principal_safe (floatCheck : Empty → Empty → Bool) (specification : Specification)
    (subject : Required.Term) (arms : List Arm) : SafeFormula (principal floatCheck specification subject arms) := by
  unfold principal generatePremises
  split
  · exact .and (CommonCaseCoreBoundedSolved.principal_safe subject arms)
      (CommonCaseConstructorBounds.safe_generateRecord specification (.var 0) ⟨rfl, rfl, rfl⟩)
  · exact .bot

theorem principal_exact (floatCheck : Empty → Empty → Bool) (specification : Specification)
    (subject : Required.Term) (arms : List Arm) (ρ : Fin 3 → Comp Common.model) :
    (principal floatCheck specification subject arms).Holds Common.model ρ ↔
      Premises [] floatCheck specification subject arms (ρ 0).1 (ρ 1).1 (ρ 2).2 :=
  generatePremises_exact floatCheck specification subject arms ρ [] [] [] (CommonSyntax.EnvRel.nil Common.model)
    (EnvRel.nil Common.model ρ) _ _ _

def solvePremises (floatCheck : Empty → Empty → Bool) (specification : Specification)
    (subject : Required.Term) (arms : List Arm) : List (CommonPatternFiniteSchemes.Scheme 3) :=
  CommonPatternFiniteSchemes.infer (principal floatCheck specification subject arms)

theorem all_parameter_premises (floatCheck : Empty → Empty → Bool) (specification : Specification)
    (subject : Required.Term) (arms : List Arm) (scheme : CommonPatternFiniteSchemes.Scheme 3)
    (member : scheme ∈ solvePremises floatCheck specification subject arms) (parameters : scheme.Parameters) :
    Premises [] floatCheck specification subject arms (scheme.instantiate parameters 0).1
      (scheme.instantiate parameters 1).1 (scheme.instantiate parameters 2).2 :=
  (principal_exact floatCheck specification subject arms _).mp
    (CommonPatternFiniteSchemes.all_parameter_holds _ scheme member parameters)

theorem premises_instances_exact (floatCheck : Empty → Empty → Bool) (specification : Specification)
    (subject : Required.Term) (arms : List Arm) (ρ : Fin 3 → Comp Common.model) :
    Premises [] floatCheck specification subject arms (ρ 0).1 (ρ 1).1 (ρ 2).2 ↔
      ∃ scheme ∈ solvePremises floatCheck specification subject arms, ∃ parameters : scheme.Parameters,
        CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters) ρ :=
  (principal_exact floatCheck specification subject arms ρ).symm.trans
    (CommonPatternFiniteSchemes.formula_instances_exact _ (principal_safe floatCheck specification subject arms) ρ)

theorem no_premises_exact (floatCheck : Empty → Empty → Bool) (specification : Specification)
    (subject : Required.Term) (arms : List Arm) : solvePremises floatCheck specification subject arms = [] ↔
      ¬ ∃ ρ : Fin 3 → Comp Common.model,
        Premises [] floatCheck specification subject arms (ρ 0).1 (ρ 1).1 (ρ 2).2 := by
  rw [solvePremises, CommonPatternFiniteSchemes.infer_empty_iff _ (principal_safe floatCheck specification subject arms)]
  exact not_congr (exists_congr (principal_exact floatCheck specification subject arms))

theorem case_prefixes (environment : List (CommonSyntax.Binding Common.model))
    (floatCheck : Empty → Empty → Bool) (specification : Specification)
    (subject : Required.Term) (arms : List Arm) (input target : Common.Ty) (cap : Common.Row)
    (premises : Premises environment floatCheck specification subject arms input target cap)
    (source : E → Common.Row) (failure : R → Common.Row)
    (evaluate : CaseValues.Bindings Empty → Required.Term → Computation E R CommonData.Value)
    (sound : EvaluationSound source failure environment evaluate) (invalid : Computation E R Bool) :
    Safe source failure
      (CommonCaseComputations.eval (ops E R) (CommonCaseFinitePrefixes.visits E R) floatCheck evaluate []
        (guardOf evaluate invalid) (fun code actual => evaluate actual code) (evaluate [] subject) (arms.map runtimeArm))
      (SuccessfulResult target) cap := by
  apply CommonCasePrefixCoverage.safe_selected_result source failure _ target cap
    (CommonCaseCorePrefixSolved.case_finite_prefixes environment subject arms input target cap premises.1
      source failure evaluate sound invalid floatCheck)
  apply CommonCasePrefixCoverage.eval_noMiss floatCheck evaluate [] (guardOf evaluate invalid)
    (fun code actual => evaluate actual code) (shapes specification) (arms.map runtimeArm)
    ((coverage_exact floatCheck specification arms).mpr premises.2.2)
  rintro value ⟨trace, present⟩
  have typed := (sound [] subject (input, cap) premises.1.1 [] .nil ⟨trace, some (.ok value)⟩ present).2 value rfl
  exact CommonCaseRecordReadout.readout specification value (Comp.pure Common.model input) typed premises.2.1

/-- Every unrestricted parameter of every returned actual scheme has
coverage, input-domain and static premises internally. Only the independent
global source-prefix contract remains; no residual/coverage/default-success
predicate is added after the solver returns. -/
theorem all_parameter_case_prefixes (floatCheck : Empty → Empty → Bool) (specification : Specification)
    (subject : Required.Term) (arms : List Arm) (scheme : CommonPatternFiniteSchemes.Scheme 3)
    (member : scheme ∈ solvePremises floatCheck specification subject arms) (parameters : scheme.Parameters)
    (source : E → Common.Row) (failure : R → Common.Row)
    (evaluate : CaseValues.Bindings Empty → Required.Term → Computation E R CommonData.Value)
    (sound : EvaluationSound source failure [] evaluate) (invalid : Computation E R Bool) :
    Safe source failure
      (CommonCaseComputations.eval (ops E R) (CommonCaseFinitePrefixes.visits E R) floatCheck evaluate []
        (guardOf evaluate invalid) (fun code actual => evaluate actual code) (evaluate [] subject) (arms.map runtimeArm))
      (SuccessfulResult (scheme.instantiate parameters 1).1) (scheme.instantiate parameters 2).2 :=
  case_prefixes [] floatCheck specification subject arms _ _ _
    (all_parameter_premises floatCheck specification subject arms scheme member parameters)
    source failure evaluate sound invalid

end Yulang.CommonCaseCoreRecordPrefixSolved
