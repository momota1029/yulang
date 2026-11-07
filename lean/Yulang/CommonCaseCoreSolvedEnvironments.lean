import Yulang.CommonCaseCoreEnvironments

/-! All finite Core arm-environment conjunctions and their actual solved list.
The independent premises below are an explicitly named factor of case typing;
in particular an empty arm list does not establish exhaustive case typing. -/

namespace Yulang.CommonCaseCoreSolvedEnvironments

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration
open CommonPatternEnvironment
open CommonPatternGenerationProvenance
open CommonPatternAllocation (ambient bindingSlots)
open CommonCaseCoreEnvironments

abbrev Arm := CasePatterns.Pattern Empty Required.Term × Option Required.Term × Required.Term

def generateAll (environment : SchemeEnv α) (subject : TyTerm α) (guardRow : RowTerm α)
    (result : CompTerm α) : List Arm → Formula α
  | [] => .top
  | (pattern, guard, body) :: rest => .and
      (generateEnvironments environment pattern guard body subject guardRow result)
      (generateAll environment subject guardRow result rest)

theorem generateAll_exact (arms : List Arm) (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic)
    (subject : TyTerm α) (guardRow : RowTerm α) (result : CompTerm α) :
    (generateAll symbolic subject guardRow result arms).Holds Common.model ρ ↔
      ∀ arm ∈ arms, EnvironmentTyping environment arm.1 arm.2.1 arm.2.2
        (subject.eval Common.model ρ) (guardRow.eval Common.model ρ) (result.eval Common.model ρ) := by
  induction arms with
  | nil => simp [generateAll, Formula.Holds]
  | cons arm rest ih =>
      rcases arm with ⟨pattern, guard, body⟩
      simp only [generateAll, Formula.Holds,
        generateEnvironments_exact pattern ρ symbolic environment semantic coreRelated symbolicRelated, ih,
        List.mem_cons, forall_eq_or_imp]

theorem safe_generateTerm (environment : SchemeEnv α) (good : SafeEnvironment environment)
    (code : Required.Term) (result : CompTerm α) (typeGood : BinderType result.ty)
    (rowGood : PresenceSourceConstraintSupport.simpleRow result.row = true) :
    SafeFormula (generateTerm environment code result) := by
  unfold generateTerm
  split
  · exact safe_generate environment good _ result typeGood rowGood
  · exact .bot

theorem safe_generateGuard (environment : SchemeEnv α) (good : SafeEnvironment environment)
    (guard : Option Required.Term) (row : RowTerm α)
    (rowGood : PresenceSourceConstraintSupport.simpleRow row = true) :
    SafeFormula (generateGuard environment guard row) := by
  cases guard with
  | none => exact ⟨trivial, rowGood, .rowLe _ _⟩
  | some code => exact safe_generateTerm environment good code _ ⟨rfl, rfl⟩ rowGood

theorem safe_consumer (pattern : CasePatterns.Pattern Empty Inference.Expr)
    (environment : SchemeEnv α) (good : SafeEnvironment environment)
    (guard : Option Required.Term) (body : Required.Term)
    (guardRow : RowTerm α) (guardGood : PresenceSourceConstraintSupport.simpleRow guardRow = true)
    (result : CompTerm α) (typeGood : BinderType result.ty)
    (rowGood : PresenceSourceConstraintSupport.simpleRow result.row = true) :
    SafeFormula (consumer pattern environment guard body guardRow result) := by
  have environmentGood := with_bindings (good.rename (ambient pattern.names.length))
    (bindingSlots pattern.names) (bindingSlots_good pattern.names)
  exact .and (safe_generateGuard _ environmentGood guard _ (by simpa using guardGood))
    (safe_generateTerm _ environmentGood body _ (typeGood.rename _)
      (by simpa only [CompTerm.rename, PresenceSourceConstraintSupport.simpleRow_rename] using rowGood))

theorem safe_generateEnvironments (environment : SchemeEnv α) (good : SafeEnvironment environment)
    (pattern : CasePatterns.Pattern Empty Required.Term) (guard : Option Required.Term) (body : Required.Term)
    (input : TyTerm α) (inputGood : Input input)
    (guardRow : RowTerm α) (guardGood : PresenceSourceConstraintSupport.simpleRow guardRow = true)
    (result : CompTerm α) (typeGood : BinderType result.ty)
    (rowGood : PresenceSourceConstraintSupport.simpleRow result.row = true) :
    SafeFormula (generateEnvironments environment pattern guard body input guardRow result) := by
  unfold generateEnvironments
  split
  · apply safe_close
    exact .and (CommonAlignedPatternGenerationProvenance.safe_constraints _ environment good []
      (by intro binding member; cases member) input inputGood)
      (safe_consumer _ environment good guard body guardRow guardGood result typeGood rowGood)
  · exact .bot

theorem safe_generateAll (arms : List Arm) (environment : SchemeEnv α) (good : SafeEnvironment environment)
    (input : TyTerm α) (inputGood : Input input)
    (guardRow : RowTerm α) (guardGood : PresenceSourceConstraintSupport.simpleRow guardRow = true)
    (result : CompTerm α) (typeGood : BinderType result.ty)
    (rowGood : PresenceSourceConstraintSupport.simpleRow result.row = true) :
    SafeFormula (generateAll environment input guardRow result arms) := by
  induction arms with
  | nil => exact .top
  | cons arm rest ih =>
      rcases arm with ⟨pattern, guard, body⟩
      exact .and (safe_generateEnvironments environment good pattern guard body input inputGood
        guardRow guardGood result typeGood rowGood) ih

def Premises (environment : List (CommonSyntax.Binding Common.model)) (subject : Required.Term)
    (arms : List Arm) (subjectResult : Comp Common.model) (guardRow : Common.Row) (result : Comp Common.model) : Prop :=
  CommonSyntax.Typing Common.model environment subject subjectResult ∧
    ∀ arm ∈ arms, EnvironmentTyping environment arm.1 arm.2.1 arm.2.2 subjectResult.1 guardRow result

def generatePremises (environment : SchemeEnv α) (subject : Required.Term) (arms : List Arm)
    (subjectResult : CompTerm α) (guardRow : RowTerm α) (result : CompTerm α) : Formula α :=
  .and (generateTerm environment subject subjectResult)
    (generateAll environment subjectResult.ty guardRow result arms)

theorem generatePremises_exact (subject : Required.Term) (arms : List Arm)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic)
    (subjectResult : CompTerm α) (guardRow : RowTerm α) (result : CompTerm α) :
    (generatePremises symbolic subject arms subjectResult guardRow result).Holds Common.model ρ ↔
      Premises environment subject arms (subjectResult.eval Common.model ρ)
        (guardRow.eval Common.model ρ) (result.eval Common.model ρ) :=
  and_congr (generateTerm_exact subject ρ symbolic environment semantic coreRelated symbolicRelated subjectResult)
    (generateAll_exact arms ρ symbolic environment semantic coreRelated symbolicRelated subjectResult.ty guardRow result)

def principal (subject : Required.Term) (arms : List Arm) : Formula (Fin 3) :=
  generatePremises [] subject arms (.var 0) (.var 1) (.var 2)

theorem principal_safe (subject : Required.Term) (arms : List Arm) : SafeFormula (principal subject arms) := by
  have good : SafeEnvironment ([] : SchemeEnv (Fin 3)) := by
    constructor <;> intro scheme member <;> cases member
  exact .and (safe_generateTerm [] good subject _ ⟨rfl, rfl⟩ rfl)
    (safe_generateAll arms [] good _ ⟨rfl, rfl, rfl⟩ _ rfl _ ⟨rfl, rfl⟩ rfl)

theorem principal_exact (subject : Required.Term) (arms : List Arm) (ρ : Fin 3 → Comp Common.model) :
    (principal subject arms).Holds Common.model ρ ↔ Premises [] subject arms (ρ 0) (ρ 1).2 (ρ 2) :=
  generatePremises_exact subject arms ρ [] [] [] (CommonSyntax.EnvRel.nil Common.model)
    (EnvRel.nil Common.model ρ) _ _ _

def solveEnvironments (subject : Required.Term) (arms : List Arm) : List (CommonPatternFiniteSchemes.Scheme 3) :=
  CommonPatternFiniteSchemes.infer (principal subject arms)

theorem all_parameter_premises (subject : Required.Term) (arms : List Arm)
    (scheme : CommonPatternFiniteSchemes.Scheme 3) (member : scheme ∈ solveEnvironments subject arms)
    (parameters : scheme.Parameters) :
    Premises [] subject arms (scheme.instantiate parameters 0) (scheme.instantiate parameters 1).2
      (scheme.instantiate parameters 2) :=
  (principal_exact subject arms _).mp (CommonPatternFiniteSchemes.all_parameter_holds _ scheme member parameters)

theorem premises_instances_exact (subject : Required.Term) (arms : List Arm) (ρ : Fin 3 → Comp Common.model) :
    Premises [] subject arms (ρ 0) (ρ 1).2 (ρ 2) ↔
      ∃ scheme ∈ solveEnvironments subject arms, ∃ parameters : scheme.Parameters,
        CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters) ρ :=
  (principal_exact subject arms ρ).symm.trans
    (CommonPatternFiniteSchemes.formula_instances_exact _ (principal_safe subject arms) ρ)

theorem no_environment_solution_exact (subject : Required.Term) (arms : List Arm) :
    solveEnvironments subject arms = [] ↔
      ¬ ∃ ρ : Fin 3 → Comp Common.model, Premises [] subject arms (ρ 0) (ρ 1).2 (ρ 2) := by
  rw [solveEnvironments, CommonPatternFiniteSchemes.infer_empty_iff _ (principal_safe subject arms)]
  exact not_congr (exists_congr (principal_exact subject arms))

end Yulang.CommonCaseCoreSolvedEnvironments
