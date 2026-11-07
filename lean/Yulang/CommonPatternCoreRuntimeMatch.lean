import Yulang.CommonPatternCoreRuntimeEnvironment

/-! Real canonical Core matches discharge the runtime compatibility part
of the row-capped finite environment formula. Interpreter adequacy remains
an explicit finite-observation contract, separate from all solver parameters.
No positional Core name-invariance assumption is introduced. -/

namespace Yulang.CommonPatternCoreRuntimeMatch

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration
open CommonPatternEnvironment
open CommonPatternTyping (valueAt bindingTypes)
open CommonPatternCoreBoundedDefaults (DefaultTyped)
open CommonPatternCoreBoundedSolved (EvaluationSound default_observations)
open CommonPatternCoreRuntimeEnvironment (Witness generateEnvironment generateEnvironment_exact)
open CommonPatternBindingAlignment (reorder)
open CommonCaseEffectPaths (observationRow)
open EvaluationTrace (Logged)
open CaseEvaluation (Event)
open CasePatterns (Pattern)
open CaseValues (Bindings BindingsHold)

theorem canonical_returns_witness (source : E → Common.Row) (failure : R → Common.Row)
    (environment : List (CommonSyntax.Binding Common.model)) (cap : Common.Row)
    (evaluate : Bindings Empty → Required.Term → Logged (Event E) R CommonData.Value)
    (sound : EvaluationSound source failure environment evaluate)
    (pattern : Pattern Empty Required.Term)
    (typed : CommonAlignedPatternTyping.Typing (DefaultTyped environment cap) prior pattern input bindings)
    (actual : Bindings Empty) (prefixTyped : BindingsHold (bindingTypes prior) actual)
    (floatCheck : Empty → Empty → Bool) (subject : CommonData.Value) (subjectTyped : valueAt input subject)
    (returned : Bindings Empty)
    (matched : (CommonPatternAlignedMatcher.run floatCheck evaluate actual pattern subject).result = .ok (some returned)) :
    Witness environment prior pattern input cap subject returned := by
  have defaults := default_observations source failure environment evaluate sound cap
  have safe := CommonAlignedPatternPartialSafety.typing_matches_partial floatCheck evaluate defaults.1
    typed.2 typed.1 actual prefixTyped subject subjectTyped
  rw [matched] at safe
  have declared : (bindingTypes bindings).map Prod.fst = pattern.names := by
    simpa only [bindingTypes, List.map_map, Function.comp_def] using typed.2.binding_names.symm
  have actualNames : returned.map Prod.fst = pattern.names := safe.names.trans declared
  have distinct : (returned.map Prod.fst).Nodup := by
    rw [actualNames]
    exact CommonPatternMatchPaths.source_names_nodup pattern typed.1
  have names : CommonPatternReturnedNames.Valid pattern.names returned :=
    ⟨distinct, fun name => by rw [actualNames]⟩
  have self : reorder pattern.names returned = returned := by
    rw [← actualNames]
    exact CommonPatternBindingAlignment.reorder_self returned distinct
  refine ⟨names, bindings, typed, subjectTyped, ?_⟩
  rw [self]
  exact safe

/-- A real successful canonical match supplies every runtime value check
internally. Core indices stay at their Q4/canonical scope throughout. -/
theorem canonical_match_models_exact (pattern : Pattern Empty Required.Term)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic) (prior : NamedTerms α)
    (input : TyTerm α) (cap : RowTerm α) (subject : CommonData.Value) (returned : Bindings Empty)
    (source : E → Common.Row) (failure : R → Common.Row)
    (evaluate : Bindings Empty → Required.Term → Logged (Event E) R CommonData.Value)
    (sound : EvaluationSound source failure environment evaluate)
    (actual : Bindings Empty) (prefixTyped : BindingsHold (bindingTypes (evalTypes ρ prior)) actual)
    (subjectTyped : valueAt (input.eval Common.model ρ) subject) (floatCheck : Empty → Empty → Bool)
    (matched : (CommonPatternAlignedMatcher.run floatCheck evaluate actual pattern subject).result = .ok (some returned)) :
    (CommonPatternCoreBoundedDefaults.generatePattern cap symbolic prior pattern input).Holds Common.model ρ ↔
      (generateEnvironment symbolic prior pattern input cap subject returned).Holds Common.model ρ := by
  rw [CommonPatternCoreBoundedDefaults.generatePattern_exact pattern cap ρ symbolic environment semantic
    coreRelated symbolicRelated prior input,
    generateEnvironment_exact pattern ρ symbolic environment semantic coreRelated symbolicRelated prior input cap subject returned]
  constructor
  · rintro ⟨bindings, typed⟩
    exact canonical_returns_witness source failure environment _ evaluate sound pattern typed actual prefixTyped
      floatCheck subject subjectTyped returned matched
  · rintro ⟨names, bindings, typed, subjectTyped, returnedTyped⟩
    exact ⟨bindings, typed⟩

/-- Every scheme parameter already supplies a compatible real subject. The
same binder witness types real returned matches and bounds all finite error /
trace observations when the independent interpreter contract is supplied. -/
theorem all_parameter_matches_partial_and_bound (pattern : Pattern Empty Required.Term) (subject : CommonData.Value)
    (returned : Bindings Empty) (scheme : CommonPatternFiniteSchemes.Scheme 2)
    (member : scheme ∈ CommonPatternCoreRuntimeEnvironment.solveEnvironments pattern subject returned)
    (parameters : scheme.Parameters) (source : E → Common.Row) (failure : R → Common.Row)
    (evaluate : Bindings Empty → Required.Term → Logged (Event E) R CommonData.Value)
    (sound : EvaluationSound source failure [] evaluate) (floatCheck : Empty → Empty → Bool) :
    ∃ bindings, CommonAlignedPatternTyping.Typing (DefaultTyped [] (scheme.instantiate parameters 1).2)
        [] pattern (scheme.instantiate parameters 0).1 bindings ∧
      CommonPatternPartialSafety.PartialHolds bindings (CommonPatternAlignedMatcher.run floatCheck evaluate [] pattern subject).result ∧
        Common.rowLe (observationRow source failure (CommonPatternAlignedMatcher.run floatCheck evaluate [] pattern subject))
          (scheme.instantiate parameters 1).2 := by
  obtain ⟨names, bindings, typed, subjectTyped, returnedTyped⟩ :=
    CommonPatternCoreRuntimeEnvironment.all_parameter_witness pattern subject returned scheme member parameters
  have bounds := CommonPatternObservationBounds.typing_partial_and_bound source failure _ floatCheck evaluate
    (default_observations source failure [] evaluate sound _) typed [] .nil subject subjectTyped
  exact ⟨bindings, typed, bounds⟩

end Yulang.CommonPatternCoreRuntimeMatch
