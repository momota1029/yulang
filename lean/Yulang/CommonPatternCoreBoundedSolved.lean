import Yulang.CommonPatternCoreBoundedDefaults

/-! The actual finite row-capped pattern family and the missing operational
interface, stated explicitly. No runtime model is manufactured for arbitrary
Core functions or effectful defaults. Every solver parameter remains free. -/

namespace Yulang.CommonPatternCoreBoundedSolved

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration
open CommonPatternEnvironment
open CommonPatternCoreBoundedDefaults
open CommonPatternTyping (valueAt bindingTypes)
open CommonPatternSourceScope (corePrefix)
open CommonPatternObservationBounds
open CommonCaseEffectPaths (observationRow)
open EvaluationTrace (Logged)
open CaseEvaluation (Event)
open CasePatterns (Pattern)

/-- The operational bridge required of a concrete Core default interpreter.
Only successful finite observations carry a value obligation; errors keep
their declared row. This contract itself is not proved for general Core. -/
def EvaluationSound (source : E → Common.Row) (failure : R → Common.Row)
    (environment : List (CommonSyntax.Binding Common.model))
    (evaluate : CaseValues.Bindings Empty → Required.Term → Logged (Event E) R CommonData.Value) : Prop :=
  ∀ types code result, CommonSyntax.Typing Common.model (corePrefix types ++ environment) code result →
    ∀ actual, CaseValues.BindingsHold (bindingTypes types) actual →
      (∀ value, (evaluate actual code).result = .ok value → valueAt result.1 value) ∧
        Common.rowLe (observationRow source failure (evaluate actual code)) result.2

theorem default_observations (source : E → Common.Row) (failure : R → Common.Row)
    (environment : List (CommonSyntax.Binding Common.model))
    (evaluate : CaseValues.Bindings Empty → Required.Term → Logged (Event E) R CommonData.Value)
    (sound : EvaluationSound source failure environment evaluate) (cap : Common.Row) :
    DefaultObservationSound source failure cap (DefaultTyped environment cap) evaluate := by
  constructor
  · intro types code type typed actual valid value evaluated
    obtain ⟨row, typed, below⟩ := typed
    exact (sound types code (type, row) typed actual valid).1 value evaluated
  · intro types code type typed actual valid
    obtain ⟨row, typed, below⟩ := typed
    exact Common.rowLe_trans (sound types code (type, row) typed actual valid).2 below

/-- Indexed Core terms use the canonical pattern interface. This operational
bound requires no name-invariance assumption on a positional interpreter. -/
theorem model_canonical_bound (pattern : Pattern Empty Required.Term) (cap : RowTerm α)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic)
    (prior : NamedTerms α) (input : TyTerm α)
    (model : (generatePattern cap symbolic prior pattern input).Holds Common.model ρ)
    (source : E → Common.Row) (failure : R → Common.Row)
    (evaluate : CaseValues.Bindings Empty → Required.Term → Logged (Event E) R CommonData.Value)
    (sound : EvaluationSound source failure environment evaluate)
    (actual : CaseValues.Bindings Empty) (valid : CaseValues.BindingsHold (bindingTypes (evalTypes ρ prior)) actual)
    (floatCheck : Empty → Empty → Bool) (value : CommonData.Value) (within : valueAt (input.eval Common.model ρ) value) :
    Common.rowLe (observationRow source failure (CommonPatternAlignedMatcher.run floatCheck evaluate actual pattern value))
      (cap.eval Common.model ρ) := by
  obtain ⟨bindings, typed⟩ := (generatePattern_exact pattern cap ρ symbolic environment semantic
    coreRelated symbolicRelated prior input).mp model
  exact typing_observation_bound source failure _ floatCheck evaluate
    (default_observations source failure environment evaluate sound _) typed.2 typed.1 actual valid value within

/-- Conditional raw-matcher transfer. Ordinary de Bruijn interpretation does
not satisfy DefaultInvariant: it needs explicit index transport. Indexed Core
integration should use model_canonical_bound instead. -/
theorem model_actual_bound (pattern : Pattern Empty Required.Term) (cap : RowTerm α)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic)
    (prior : NamedTerms α) (input : TyTerm α)
    (model : (generatePattern cap symbolic prior pattern input).Holds Common.model ρ)
    (source : E → Common.Row) (failure : R → Common.Row)
    (evaluate : CaseValues.Bindings Empty → Required.Term → Logged (Event E) R CommonData.Value)
    (sound : EvaluationSound source failure environment evaluate)
    (invariant : CommonPatternAlignedMatcher.DefaultInvariant evaluate)
    (actual : CaseValues.Bindings Empty) (valid : CaseValues.BindingsHold (bindingTypes (evalTypes ρ prior)) actual)
    (floatCheck : Empty → Empty → Bool) (value : CommonData.Value) (within : valueAt (input.eval Common.model ρ) value) :
    Common.rowLe (observationRow source failure (ScopedCasePatterns.run floatCheck evaluate actual pattern value))
      (cap.eval Common.model ρ) := by
  obtain ⟨bindings, typed⟩ := (generatePattern_exact pattern cap ρ symbolic environment semantic
    coreRelated symbolicRelated prior input).mp model
  exact actual_typing_observation_bound source failure _ floatCheck evaluate invariant
    (default_observations source failure environment evaluate sound _) typed actual valid value within

def principal (pattern : Pattern Empty Required.Term) : Formula (Fin 2) :=
  generatePattern (.var 1) [] [] pattern (.var 0)

theorem principal_safe (pattern : Pattern Empty Required.Term) :
    CommonPatternGenerationProvenance.SafeFormula (principal pattern) := by
  have good : CommonPatternGenerationProvenance.SafeEnvironment ([] : SchemeEnv (Fin 2)) := by
    constructor <;> intro scheme member <;> cases member
  exact safe_generatePattern (.var 1) rfl [] good [] (by intro binding member; cases member) pattern _ ⟨rfl, rfl, rfl⟩

def HasPattern (pattern : Pattern Empty Required.Term) (input : Common.Ty) (cap : Common.Row) : Prop :=
  ∃ bindings, CommonAlignedPatternTyping.Typing (DefaultTyped [] cap) [] pattern input bindings

theorem principal_exact (pattern : Pattern Empty Required.Term) (ρ : Fin 2 → Comp Common.model) :
    (principal pattern).Holds Common.model ρ ↔ HasPattern pattern (ρ 0).1 (ρ 1).2 :=
  generatePattern_exact pattern (.var 1) ρ [] [] [] (CommonSyntax.EnvRel.nil Common.model)
    (EnvRel.nil Common.model ρ) [] _

def solvePatterns (pattern : Pattern Empty Required.Term) : List (CommonPatternFiniteSchemes.Scheme 2) :=
  CommonPatternFiniteSchemes.infer (principal pattern)

theorem all_parameter_patterns (pattern : Pattern Empty Required.Term) (scheme : CommonPatternFiniteSchemes.Scheme 2)
    (member : scheme ∈ solvePatterns pattern) (parameters : scheme.Parameters) :
    HasPattern pattern (scheme.instantiate parameters 0).1 (scheme.instantiate parameters 1).2 :=
  (principal_exact pattern _).mp (CommonPatternFiniteSchemes.all_parameter_holds _ scheme member parameters)

theorem pattern_instances_exact (pattern : Pattern Empty Required.Term) (ρ : Fin 2 → Comp Common.model) :
    HasPattern pattern (ρ 0).1 (ρ 1).2 ↔
      ∃ scheme ∈ solvePatterns pattern, ∃ parameters : scheme.Parameters,
        CommonPatternFormulaEquivalence.AssignmentEquivalent (scheme.instantiate parameters) ρ :=
  (principal_exact pattern ρ).symm.trans
    (CommonPatternFiniteSchemes.formula_instances_exact _ (principal_safe pattern) ρ)

theorem no_pattern_exact (pattern : Pattern Empty Required.Term) : solvePatterns pattern = [] ↔
    ¬ ∃ ρ : Fin 2 → Comp Common.model, HasPattern pattern (ρ 0).1 (ρ 1).2 := by
  rw [solvePatterns, CommonPatternFiniteSchemes.infer_empty_iff _ (principal_safe pattern)]
  exact not_congr (exists_congr (principal_exact pattern))

theorem all_parameter_canonical_bound (pattern : Pattern Empty Required.Term)
    (scheme : CommonPatternFiniteSchemes.Scheme 2) (member : scheme ∈ solvePatterns pattern)
    (parameters : scheme.Parameters) (source : E → Common.Row) (failure : R → Common.Row)
    (evaluate : CaseValues.Bindings Empty → Required.Term → Logged (Event E) R CommonData.Value)
    (sound : EvaluationSound source failure [] evaluate)
    (floatCheck : Empty → Empty → Bool) (value : CommonData.Value)
    (within : valueAt (scheme.instantiate parameters 0).1 value) :
    Common.rowLe (observationRow source failure (CommonPatternAlignedMatcher.run floatCheck evaluate [] pattern value))
      (scheme.instantiate parameters 1).2 := by
  obtain ⟨bindings, typed⟩ := all_parameter_patterns pattern scheme member parameters
  exact typing_observation_bound source failure _ floatCheck evaluate
    (default_observations source failure [] evaluate sound _) typed.2 typed.1 [] .nil value within

/-- Conditional integration: every real returned scheme and every arbitrary
parameter supplies the bound when a concrete interpreter supplies the stated
operational bridge AND name invariance. A normal positional Core interpreter
needs all_parameter_canonical_bound or explicit index transport instead.
The bridges are independent of the solver parameters. -/
theorem all_parameter_actual_bound (pattern : Pattern Empty Required.Term)
    (scheme : CommonPatternFiniteSchemes.Scheme 2) (member : scheme ∈ solvePatterns pattern)
    (parameters : scheme.Parameters) (source : E → Common.Row) (failure : R → Common.Row)
    (evaluate : CaseValues.Bindings Empty → Required.Term → Logged (Event E) R CommonData.Value)
    (sound : EvaluationSound source failure [] evaluate)
    (invariant : CommonPatternAlignedMatcher.DefaultInvariant evaluate)
    (floatCheck : Empty → Empty → Bool) (value : CommonData.Value)
    (within : valueAt (scheme.instantiate parameters 0).1 value) :
    Common.rowLe (observationRow source failure (ScopedCasePatterns.run floatCheck evaluate [] pattern value))
      (scheme.instantiate parameters 1).2 := by
  obtain ⟨bindings, typed⟩ := all_parameter_patterns pattern scheme member parameters
  exact actual_typing_observation_bound source failure _ floatCheck evaluate invariant
    (default_observations source failure [] evaluate sound _) typed [] .nil value within

end Yulang.CommonPatternCoreBoundedSolved
