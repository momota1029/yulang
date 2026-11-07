import Yulang.CommonPatternRuntimeValueConstraints

/-! One source allocation checks the pattern and actual subject/returned
value types with identical binder references. This is a type-environment iff;
it does not claim that arbitrary supplied values are an actual match result. -/

namespace Yulang.CommonPatternSourceRuntimeEnvironment

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration
open CommonPatternEnvironment
open CommonPatternAllocation (Slots ambient assignment assignment_ambient bindingSlots bindingSlots_eval bindingValues bindingValues_complete)
open CommonPatternSourceElaboration (DefaultTyped elaborate covered names_elaborate)
open CommonPatternBindingAlignment (reorder)
open CommonPatternRuntimeValueConstraints (valueConstraints bindingConstraints value_constraints_exact binding_constraints_exact)
open CommonPatternTyping (valueAt bindingTypes)
open CasePatterns (Pattern)

def consumer (pattern : Pattern Empty Inference.Expr) (input : TyTerm α)
    (subject : CommonData.Value) (returned : CaseValues.Bindings Empty) : Formula (Slots α pattern.names.length) :=
  .and (valueConstraints subject (input.rename (ambient pattern.names.length)))
    (bindingConstraints (bindingSlots pattern.names) (reorder pattern.names returned))

theorem consumer_exact (pattern : Pattern Empty Inference.Expr) (input : TyTerm α)
    (subject : CommonData.Value) (returned : CaseValues.Bindings Empty)
    (ρ : α → Comp Common.model) (values : Fin pattern.names.length → Comp Common.model) :
    (consumer pattern input subject returned).Holds Common.model (assignment ρ values) ↔
      valueAt (input.eval Common.model ρ) subject ∧
      CaseValues.BindingsHold (bindingTypes (bindingValues pattern.names values)) (reorder pattern.names returned) := by
  simp only [consumer, Formula.Holds, value_constraints_exact, binding_constraints_exact,
    TyTerm.eval_rename, assignment_ambient, bindingSlots_eval]

def Witness (outerNames : List Nat) (environment : List (CommonSyntax.Binding Common.model))
    (prior : NamedTypes) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (input : Common.Ty) (subject : CommonData.Value) (returned : CaseValues.Bindings Empty) : Prop :=
  ∃ bindings, CommonAlignedPatternTyping.Typing (DefaultTyped outerNames environment) prior pattern input bindings ∧
    valueAt input subject ∧ CaseValues.BindingsHold (bindingTypes bindings) (reorder pattern.names returned)

def generateEnvironment (outerNames : List Nat) (environment : SchemeEnv α) (prior : NamedTerms α)
    (pattern : Pattern Empty (CaseDataTerms.Expr Empty)) (input : TyTerm α)
    (subject : CommonData.Value) (returned : CaseValues.Bindings Empty) : Formula α :=
  let scope := prior.map Prod.fst ++ outerNames
  if PatternBindingChecks.check pattern && covered scope pattern then
    let lowered := elaborate scope pattern
    CommonAlignedPatternAllocation.withPattern lowered environment prior input (consumer lowered input subject returned)
  else .bot

/-- Arbitrary source patterns/defaults, cumulative prefixes, captured
environments, Common assignments, actual subject and literal returned values.
One allocation witnesses both the independent typing and real-value type
compatibility. A runtime-match equality is neither hidden nor inferred. -/
theorem generateEnvironment_exact (pattern : Pattern Empty (CaseDataTerms.Expr Empty)) (outerNames : List Nat)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic)
    (prior : NamedTerms α) (input : TyTerm α) (subject : CommonData.Value) (returned : CaseValues.Bindings Empty) :
    (generateEnvironment outerNames symbolic prior pattern input subject returned).Holds Common.model ρ ↔
      Witness outerNames environment (evalTypes ρ prior) pattern (input.eval Common.model ρ) subject returned := by
  have patternExact := CommonPatternSourceElaboration.raw_typing_exact (outerNames := outerNames) coreRelated
    pattern (evalTypes ρ prior) (input.eval Common.model ρ)
  simp only [evalTypes_names] at patternExact
  have canonical : reorder (elaborate (prior.map Prod.fst ++ outerNames) pattern).names returned =
      reorder pattern.names returned := congrArg (fun names => reorder names returned) (names_elaborate _ pattern)
  cases checked : PatternBindingChecks.check pattern && covered (prior.map Prod.fst ++ outerNames) pattern with
  | false =>
      simp only [generateEnvironment, checked, Bool.false_eq_true, ↓reduceIte, Formula.Holds]
      constructor
      · exact False.elim
      · rintro ⟨bindings, typed, subjectTyped, returnedTyped⟩
        have valid := (PatternBindingChecks.check_exact pattern).mpr typed.1
        have within := ((patternExact bindings).mp typed.2).1
        simp [valid, within] at checked
  | true =>
      have gate := Bool.and_eq_true_iff.mp checked
      have valid := (PatternBindingChecks.check_exact pattern).mp gate.1
      simp only [generateEnvironment, checked, ↓reduceIte,
        CommonAlignedPatternAllocation.withPattern_exact _ ρ symbolic semantic symbolicRelated,
        consumer_exact, canonical]
      constructor
      · rintro ⟨values, typed, subjectTyped, returnedTyped⟩
        exact ⟨_, ⟨valid, (patternExact _).mpr ⟨gate.2, typed⟩⟩, subjectTyped, returnedTyped⟩
      · rintro ⟨bindings, typed, subjectTyped, returnedTyped⟩
        have raw := ((patternExact bindings).mp typed.2).2
        obtain ⟨values, same⟩ := bindingValues_complete (elaborate (prior.map Prod.fst ++ outerNames) pattern).names bindings
          (typed.2.binding_names.symm.trans (names_elaborate _ pattern).symm)
        exact ⟨values, same.symm ▸ raw, subjectTyped, same.symm ▸ returnedTyped⟩

open CommonPatternGenerationProvenance (SafeEnvironment SafeFormula GoodBindings BinderType)

theorem safe_consumer (pattern : Pattern Empty Inference.Expr) (input : TyTerm α) (good : BinderType input)
    (subject : CommonData.Value) (returned : CaseValues.Bindings Empty) :
    SafeFormula (consumer pattern input subject returned) :=
  .and (CommonPatternRuntimeValueConstraints.safe_valueConstraints subject _ (good.rename _))
    (CommonPatternRuntimeValueConstraints.safe_bindingConstraints (bindingSlots pattern.names)
      (CommonPatternGenerationProvenance.bindingSlots_good pattern.names) _)

theorem safe_generateEnvironment (outerNames : List Nat) (environment : SchemeEnv α) (good : SafeEnvironment environment)
    (prior : NamedTerms α) (priorGood : GoodBindings prior) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (input : TyTerm α) (inputGood : BinderType input) (subject : CommonData.Value) (returned : CaseValues.Bindings Empty) :
    SafeFormula (generateEnvironment outerNames environment prior pattern input subject returned) := by
  unfold generateEnvironment
  dsimp only
  split
  · apply CommonPatternGenerationProvenance.safe_close
    exact .and (CommonAlignedPatternGenerationProvenance.safe_constraints _ environment good prior priorGood input inputGood.input)
      (safe_consumer _ input inputGood subject returned)
  · exact .bot

def principal (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (subject : CommonData.Value) (returned : CaseValues.Bindings Empty) : Formula (Fin 1) :=
  generateEnvironment outerNames [] [] pattern (.var 0) subject returned

theorem principal_safe (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (subject : CommonData.Value) (returned : CaseValues.Bindings Empty) :
    SafeFormula (principal outerNames pattern subject returned) := by
  have good : SafeEnvironment ([] : SchemeEnv (Fin 1)) := by
    constructor <;> intro scheme member <;> cases member
  exact safe_generateEnvironment outerNames [] good [] (by intro binding member; cases member) pattern _ ⟨rfl, rfl⟩ subject returned

theorem principal_exact (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (subject : CommonData.Value) (returned : CaseValues.Bindings Empty) (ρ : Fin 1 → Comp Common.model) :
    (principal outerNames pattern subject returned).Holds Common.model ρ ↔
      Witness outerNames [] [] pattern (ρ 0).1 subject returned :=
  generateEnvironment_exact pattern outerNames ρ [] [] [] (CommonSyntax.EnvRel.nil Common.model)
    (EnvRel.nil Common.model ρ) [] _ subject returned

def solveEnvironments (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (subject : CommonData.Value) (returned : CaseValues.Bindings Empty) : List (CommonPatternFiniteSchemes.Scheme 1) :=
  CommonPatternFiniteSchemes.infer (principal outerNames pattern subject returned)

/-- Every returned unrestricted instance checks the same actual subject and
literal returned values; its binder references are not independently chosen
between typing, defaults and runtime value constraints. -/
theorem all_parameter_witness (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (subject : CommonData.Value) (returned : CaseValues.Bindings Empty) (scheme : CommonPatternFiniteSchemes.Scheme 1)
    (member : scheme ∈ solveEnvironments outerNames pattern subject returned) (parameters : scheme.Parameters) :
    Witness outerNames [] [] pattern (scheme.instantiate parameters 0).1 subject returned :=
  (principal_exact outerNames pattern subject returned _).mp
    (CommonPatternFiniteSchemes.all_parameter_holds _ scheme member parameters)

theorem witness_instances_exact (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (subject : CommonData.Value) (returned : CaseValues.Bindings Empty) (ρ : Fin 1 → Comp Common.model) :
    Witness outerNames [] [] pattern (ρ 0).1 subject returned ↔
      ∃ scheme ∈ solveEnvironments outerNames pattern subject returned, ∃ parameters : scheme.Parameters,
        CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters) ρ :=
  (principal_exact outerNames pattern subject returned ρ).symm.trans
    (CommonPatternFiniteSchemes.formula_instances_exact _ (principal_safe outerNames pattern subject returned) ρ)

theorem no_witness_exact (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (subject : CommonData.Value) (returned : CaseValues.Bindings Empty) :
    solveEnvironments outerNames pattern subject returned = [] ↔
      ¬ ∃ ρ : Fin 1 → Comp Common.model, Witness outerNames [] [] pattern (ρ 0).1 subject returned := by
  rw [solveEnvironments, CommonPatternFiniteSchemes.infer_empty_iff _ (principal_safe outerNames pattern subject returned)]
  exact not_congr (exists_congr (principal_exact outerNames pattern subject returned))

end Yulang.CommonPatternSourceRuntimeEnvironment
