import Yulang.CommonPatternCoreBoundedSolved
import Yulang.CommonPatternCheckedRuntimeEnvironment

/-! One real Core pattern allocation retains its default row cap, actual
subject compatibility and every raw returned payload. Core terms already
use their Q4 indices. Values remain the old Common data carrier; arbitrary
supplied bindings are not silently identified with an actual match result. -/

namespace Yulang.CommonPatternCoreRuntimeEnvironment

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration
open CommonPatternEnvironment
open CommonPatternAllocation (Slots ambient assignment bindingValues bindingValues_complete)
open CommonPatternCoreBoundedDefaults (DefaultTyped lower covered names_lower)
open CommonPatternTyping (valueAt bindingTypes)
open CommonPatternBindingAlignment (reorder)
open CommonPatternSourceRuntimeEnvironment (consumer consumer_exact safe_consumer)
open CasePatterns (Pattern)
open CaseValues (Bindings BindingsHold)

def Witness (environment : List (CommonSyntax.Binding Common.model)) (prior : NamedTypes)
    (pattern : Pattern Empty Required.Term) (input : Common.Ty) (cap : Common.Row)
    (subject : CommonData.Value) (returned : Bindings Empty) : Prop :=
  CommonPatternReturnedNames.Valid pattern.names returned ∧ ∃ bindings,
    CommonAlignedPatternTyping.Typing (DefaultTyped environment cap) prior pattern input bindings ∧
      valueAt input subject ∧ BindingsHold (bindingTypes bindings) (reorder pattern.names returned)

def generateEnvironment (environment : SchemeEnv α) (prior : NamedTerms α) (pattern : Pattern Empty Required.Term)
    (input : TyTerm α) (cap : RowTerm α) (subject : CommonData.Value) (returned : Bindings Empty) : Formula α :=
  if CommonPatternReturnedNames.check pattern.names returned && PatternBindingChecks.check pattern && covered pattern then
    let lowered := lower pattern
    CommonPatternBoundedAllocation.withPattern lowered cap environment prior input (consumer lowered input subject returned)
  else .bot

theorem generateEnvironment_exact (pattern : Pattern Empty Required.Term)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic) (prior : NamedTerms α)
    (input : TyTerm α) (cap : RowTerm α) (subject : CommonData.Value) (returned : Bindings Empty) :
    (generateEnvironment symbolic prior pattern input cap subject returned).Holds Common.model ρ ↔
      Witness environment (evalTypes ρ prior) pattern (input.eval Common.model ρ) (cap.eval Common.model ρ) subject returned := by
  have patternExact := CommonPatternCoreBoundedDefaults.raw_typing_exact coreRelated (cap.eval Common.model ρ)
    pattern (evalTypes ρ prior) (input.eval Common.model ρ)
  have canonical : reorder (lower pattern).names returned = reorder pattern.names returned := by rw [names_lower]
  cases checked : CommonPatternReturnedNames.check pattern.names returned && PatternBindingChecks.check pattern && covered pattern with
  | false =>
      simp only [generateEnvironment, checked, Bool.false_eq_true, ↓reduceIte, Formula.Holds]
      constructor
      · exact False.elim
      · rintro ⟨names, bindings, typed, subjectTyped, returnedTyped⟩
        have valid := (PatternBindingChecks.check_exact pattern).mpr typed.1
        have within := ((patternExact bindings).mp typed.2).1
        have returnedNames := (CommonPatternReturnedNames.check_exact pattern.names returned).mpr names
        simp [returnedNames, valid, within] at checked
  | true =>
      have gates := Bool.and_eq_true_iff.mp checked
      have namesAndBindings := Bool.and_eq_true_iff.mp gates.1
      have names := (CommonPatternReturnedNames.check_exact pattern.names returned).mp namesAndBindings.1
      have valid := (PatternBindingChecks.check_exact pattern).mp namesAndBindings.2
      simp only [generateEnvironment, checked, ↓reduceIte,
        CommonPatternBoundedAllocation.withPattern_exact _ cap ρ symbolic semantic symbolicRelated,
        consumer_exact, canonical]
      constructor
      · rintro ⟨values, typed, subjectTyped, returnedTyped⟩
        exact ⟨names, _, ⟨valid, (patternExact _).mpr ⟨gates.2, typed⟩⟩, subjectTyped, returnedTyped⟩
      · rintro ⟨returnedNames, bindings, typed, subjectTyped, returnedTyped⟩
        have raw := ((patternExact bindings).mp typed.2).2
        obtain ⟨values, same⟩ := bindingValues_complete (lower pattern).names bindings
          (typed.2.binding_names.symm.trans (names_lower pattern).symm)
        exact ⟨values, same.symm ▸ raw, subjectTyped, same.symm ▸ returnedTyped⟩

open CommonPatternGenerationProvenance (SafeEnvironment SafeFormula GoodBindings BinderType)

theorem safe_generateEnvironment (environment : SchemeEnv α) (environmentGood : SafeEnvironment environment)
    (prior : NamedTerms α) (priorGood : GoodBindings prior) (pattern : Pattern Empty Required.Term)
    (input : TyTerm α) (inputGood : BinderType input) (cap : RowTerm α)
    (capGood : PresenceSourceConstraintSupport.simpleRow cap = true) (subject : CommonData.Value) (returned : Bindings Empty) :
    SafeFormula (generateEnvironment environment prior pattern input cap subject returned) := by
  unfold generateEnvironment
  split
  · apply CommonPatternGenerationProvenance.safe_close
    exact .and (CommonPatternBoundedProvenance.safe_constraints _ cap capGood environment environmentGood prior priorGood input inputGood.input)
      (safe_consumer _ input inputGood subject returned)
  · exact .bot

def principal (pattern : Pattern Empty Required.Term) (subject : CommonData.Value) (returned : Bindings Empty) : Formula (Fin 2) :=
  generateEnvironment [] [] pattern (.var 0) (.var 1) subject returned

theorem principal_safe (pattern : Pattern Empty Required.Term) (subject : CommonData.Value) (returned : Bindings Empty) :
    SafeFormula (principal pattern subject returned) := by
  have environmentGood : SafeEnvironment ([] : SchemeEnv (Fin 2)) := by
    constructor <;> intro scheme member <;> cases member
  exact safe_generateEnvironment [] environmentGood [] (by intro binding member; cases member) pattern _ ⟨rfl, rfl⟩ _ rfl subject returned

theorem principal_exact (pattern : Pattern Empty Required.Term) (subject : CommonData.Value) (returned : Bindings Empty)
    (ρ : Fin 2 → Comp Common.model) :
    (principal pattern subject returned).Holds Common.model ρ ↔ Witness [] [] pattern (ρ 0).1 (ρ 1).2 subject returned :=
  generateEnvironment_exact pattern ρ [] [] [] (CommonSyntax.EnvRel.nil Common.model) (EnvRel.nil Common.model ρ) [] _ _ subject returned

def solveEnvironments (pattern : Pattern Empty Required.Term) (subject : CommonData.Value) (returned : Bindings Empty) :
    List (CommonPatternFiniteSchemes.Scheme 2) := CommonPatternFiniteSchemes.infer (principal pattern subject returned)

theorem all_parameter_witness (pattern : Pattern Empty Required.Term) (subject : CommonData.Value) (returned : Bindings Empty)
    (scheme : CommonPatternFiniteSchemes.Scheme 2) (member : scheme ∈ solveEnvironments pattern subject returned)
    (parameters : scheme.Parameters) :
    Witness [] [] pattern (scheme.instantiate parameters 0).1 (scheme.instantiate parameters 1).2 subject returned :=
  (principal_exact pattern subject returned _).mp (CommonPatternFiniteSchemes.all_parameter_holds _ scheme member parameters)

theorem witness_instances_exact (pattern : Pattern Empty Required.Term) (subject : CommonData.Value) (returned : Bindings Empty)
    (ρ : Fin 2 → Comp Common.model) : Witness [] [] pattern (ρ 0).1 (ρ 1).2 subject returned ↔
      ∃ scheme ∈ solveEnvironments pattern subject returned, ∃ parameters : scheme.Parameters,
        CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters) ρ :=
  (principal_exact pattern subject returned ρ).symm.trans
    (CommonPatternFiniteSchemes.formula_instances_exact _ (principal_safe pattern subject returned) ρ)

theorem no_witness_exact (pattern : Pattern Empty Required.Term) (subject : CommonData.Value) (returned : Bindings Empty) :
    solveEnvironments pattern subject returned = [] ↔
      ¬ ∃ ρ : Fin 2 → Comp Common.model, Witness [] [] pattern (ρ 0).1 (ρ 1).2 subject returned := by
  rw [solveEnvironments, CommonPatternFiniteSchemes.infer_empty_iff _ (principal_safe pattern subject returned)]
  exact not_congr (exists_congr (principal_exact pattern subject returned))

theorem all_parameter_values_preserved (pattern : Pattern Empty Required.Term) (subject : CommonData.Value) (returned : Bindings Empty)
    (scheme : CommonPatternFiniteSchemes.Scheme 2) (member : scheme ∈ solveEnvironments pattern subject returned)
    (parameters : scheme.Parameters) : (reorder pattern.names returned).Perm returned := by
  obtain ⟨names, bindings, typed, subjectTyped, returnedTyped⟩ := all_parameter_witness pattern subject returned scheme member parameters
  exact CommonPatternReturnedNames.reorder_perm pattern.names (CommonPatternMatchPaths.source_names_nodup pattern typed.1) returned names

end Yulang.CommonPatternCoreRuntimeEnvironment
