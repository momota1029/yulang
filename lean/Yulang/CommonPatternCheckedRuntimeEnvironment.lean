import Yulang.CommonPatternReturnedNames
import Yulang.CommonPatternSourceRuntimeMatch

/-! Whole raw returned-name validation before canonical type checking.
The preceding projection interface remains available with its stated scope;
this stronger wrapper cannot discard an extra/hidden returned payload. -/

namespace Yulang.CommonPatternCheckedRuntimeEnvironment

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration
open CommonPatternEnvironment
open CommonPatternTyping (bindingTypes valueAt)
open CommonPatternDataSafety (EnvironmentHolds)
open CasePatterns (Pattern)
open CaseValues (Bindings BindingsHold)

def Witness (outerNames : List Nat) (environment : List (CommonSyntax.Binding Common.model))
    (prior : NamedTypes) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (input : Common.Ty) (subject : CommonData.Value) (returned : Bindings Empty) : Prop :=
  CommonPatternReturnedNames.Valid pattern.names returned ∧
    CommonPatternSourceRuntimeEnvironment.Witness outerNames environment prior pattern input subject returned

def generateEnvironment (outerNames : List Nat) (environment : SchemeEnv α) (prior : NamedTerms α)
    (pattern : Pattern Empty (CaseDataTerms.Expr Empty)) (input : TyTerm α)
    (subject : CommonData.Value) (returned : Bindings Empty) : Formula α :=
  if CommonPatternReturnedNames.check pattern.names returned then
    CommonPatternSourceRuntimeEnvironment.generateEnvironment outerNames environment prior pattern input subject returned
  else .bot

theorem generateEnvironment_exact (pattern : Pattern Empty (CaseDataTerms.Expr Empty)) (outerNames : List Nat)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic)
    (prior : NamedTerms α) (input : TyTerm α) (subject : CommonData.Value) (returned : Bindings Empty) :
    (generateEnvironment outerNames symbolic prior pattern input subject returned).Holds Common.model ρ ↔
      Witness outerNames environment (evalTypes ρ prior) pattern (input.eval Common.model ρ) subject returned := by
  cases checked : CommonPatternReturnedNames.check pattern.names returned with
  | false =>
      have invalid : ¬ CommonPatternReturnedNames.Valid pattern.names returned := by
        intro valid
        have accepted := (CommonPatternReturnedNames.check_exact pattern.names returned).mpr valid
        rw [checked] at accepted
        cases accepted
      simp only [generateEnvironment, checked, Bool.false_eq_true, ↓reduceIte, Formula.Holds, Witness, invalid, false_and]
  | true =>
      have valid := (CommonPatternReturnedNames.check_exact pattern.names returned).mp checked
      simp only [generateEnvironment, checked, ↓reduceIte,
        CommonPatternSourceRuntimeEnvironment.generateEnvironment_exact pattern outerNames ρ symbolic environment semantic
          coreRelated symbolicRelated prior input subject returned, Witness, valid, true_and]

/-- A model checks every raw name and every raw payload. Canonicalization is
a literal permutation of the entire returned list, not a lossy projection. -/
theorem all_values_preserved (pattern : Pattern Empty (CaseDataTerms.Expr Empty)) (outerNames : List Nat)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic)
    (prior : NamedTerms α) (input : TyTerm α) (subject : CommonData.Value) (returned : Bindings Empty)
    (models : (generateEnvironment outerNames symbolic prior pattern input subject returned).Holds Common.model ρ) :
    (CommonPatternBindingAlignment.reorder pattern.names returned).Perm returned := by
  obtain ⟨names, bindings, typed, subjectTyped, returnedTyped⟩ :=
    (generateEnvironment_exact pattern outerNames ρ symbolic environment semantic coreRelated symbolicRelated prior input subject returned).mp models
  exact CommonPatternReturnedNames.reorder_perm pattern.names
    (CommonPatternMatchPaths.source_names_nodup pattern typed.1) returned names

/-- No new assumption about returned names is required at a real match: Q7
and the actual match path discharge the added finite raw-name check. -/
theorem actual_match_models_exact (pattern : Pattern Empty (CaseDataTerms.Expr Empty)) (outerNames : List Nat)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic)
    (actualOuter : Bindings Empty) (outer : EnvironmentHolds outerNames environment actualOuter)
    (prior : NamedTerms α) (actualPrefix : Bindings Empty)
    (prefixTyped : BindingsHold (bindingTypes (evalTypes ρ prior)) actualPrefix)
    (input : TyTerm α) (subject : CommonData.Value) (subjectTyped : valueAt (input.eval Common.model ρ) subject)
    (floatCheck : Empty → Empty → Bool) (returned : Bindings Empty)
    (matched : (ScopedCasePatterns.run floatCheck CaseDataTerms.defaultEval (actualPrefix ++ actualOuter) pattern subject).result =
      .ok (some returned)) :
    (CommonPatternSourceElaboration.generateSourcePattern outerNames symbolic prior pattern input).Holds Common.model ρ ↔
      (generateEnvironment outerNames symbolic prior pattern input subject returned).Holds Common.model ρ := by
  have original := CommonPatternSourceRuntimeMatch.actual_match_models_exact pattern outerNames ρ symbolic environment semantic
    coreRelated symbolicRelated actualOuter outer prior actualPrefix prefixTyped input subject subjectTyped floatCheck returned matched
  constructor
  · intro models
    obtain ⟨bindings, typed⟩ := (CommonPatternSourceElaboration.generateSourcePattern_exact pattern outerNames ρ symbolic environment semantic
      coreRelated symbolicRelated prior input).mp models
    have valid := CommonPatternReturnedNames.actual_return_valid floatCheck CaseDataTerms.defaultEval pattern typed.1
      (actualPrefix ++ actualOuter) subject returned matched
    simp only [generateEnvironment, (CommonPatternReturnedNames.check_exact pattern.names returned).mpr valid, ↓reduceIte]
    exact original.mp models
  · intro models
    have valid := (generateEnvironment_exact pattern outerNames ρ symbolic environment semantic coreRelated symbolicRelated prior input subject returned).mp models
    exact original.mpr ((CommonPatternSourceRuntimeEnvironment.generateEnvironment_exact pattern outerNames ρ symbolic environment semantic
      coreRelated symbolicRelated prior input subject returned).mpr valid.2)

def principal (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (subject : CommonData.Value) (returned : Bindings Empty) : Formula (Fin 1) :=
  generateEnvironment outerNames [] [] pattern (.var 0) subject returned

theorem principal_safe (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (subject : CommonData.Value) (returned : Bindings Empty) : CommonPatternGenerationProvenance.SafeFormula (principal outerNames pattern subject returned) := by
  unfold principal generateEnvironment
  split
  · exact CommonPatternSourceRuntimeEnvironment.principal_safe outerNames pattern subject returned
  · exact .bot

theorem principal_exact (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (subject : CommonData.Value) (returned : Bindings Empty) (ρ : Fin 1 → Comp Common.model) :
    (principal outerNames pattern subject returned).Holds Common.model ρ ↔ Witness outerNames [] [] pattern (ρ 0).1 subject returned :=
  generateEnvironment_exact pattern outerNames ρ [] [] [] (CommonSyntax.EnvRel.nil Common.model)
    (EnvRel.nil Common.model ρ) [] _ subject returned

def solveEnvironments (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (subject : CommonData.Value) (returned : Bindings Empty) : List (CommonPatternFiniteSchemes.Scheme 1) :=
  CommonPatternFiniteSchemes.infer (principal outerNames pattern subject returned)

theorem witness_instances_exact (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (subject : CommonData.Value) (returned : Bindings Empty) (ρ : Fin 1 → Comp Common.model) :
    Witness outerNames [] [] pattern (ρ 0).1 subject returned ↔
      ∃ scheme ∈ solveEnvironments outerNames pattern subject returned, ∃ parameters : scheme.Parameters,
        CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters) ρ :=
  (principal_exact outerNames pattern subject returned ρ).symm.trans
    (CommonPatternFiniteSchemes.formula_instances_exact _ (principal_safe outerNames pattern subject returned) ρ)

theorem all_parameter_witness (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (subject : CommonData.Value) (returned : Bindings Empty) (scheme : CommonPatternFiniteSchemes.Scheme 1)
    (member : scheme ∈ solveEnvironments outerNames pattern subject returned) (parameters : scheme.Parameters) :
    Witness outerNames [] [] pattern (scheme.instantiate parameters 0).1 subject returned :=
  (principal_exact outerNames pattern subject returned _).mp (CommonPatternFiniteSchemes.all_parameter_holds _ scheme member parameters)

theorem all_parameter_values_preserved (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (subject : CommonData.Value) (returned : Bindings Empty) (scheme : CommonPatternFiniteSchemes.Scheme 1)
    (member : scheme ∈ solveEnvironments outerNames pattern subject returned) (parameters : scheme.Parameters) :
    (CommonPatternBindingAlignment.reorder pattern.names returned).Perm returned := by
  obtain ⟨names, bindings, typed, subjectTyped, returnedTyped⟩ := all_parameter_witness outerNames pattern subject returned scheme member parameters
  exact CommonPatternReturnedNames.reorder_perm pattern.names (CommonPatternMatchPaths.source_names_nodup pattern typed.1) returned names

theorem no_witness_exact (outerNames : List Nat) (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (subject : CommonData.Value) (returned : Bindings Empty) :
    solveEnvironments outerNames pattern subject returned = [] ↔
      ¬ ∃ ρ : Fin 1 → Comp Common.model, Witness outerNames [] [] pattern (ρ 0).1 subject returned := by
  rw [solveEnvironments, CommonPatternFiniteSchemes.infer_empty_iff _ (principal_safe outerNames pattern subject returned)]
  exact not_congr (exists_congr (principal_exact outerNames pattern subject returned))

/-- The lossy-projection probe is rejected before any value constraint is
generated, even if the extra value has no old Common structural typing. -/
theorem wildcard_extra_rejected (outerNames : List Nat) (environment : SchemeEnv α) (prior : NamedTerms α)
    (input : TyTerm α) (subject value : CommonData.Value) (name : Nat) (ρ : α → Comp Common.model) :
    ¬ (generateEnvironment outerNames environment prior .wildcard input subject [(name, value)]).Holds Common.model ρ := by
  change ¬ False
  exact not_false

end Yulang.CommonPatternCheckedRuntimeEnvironment
