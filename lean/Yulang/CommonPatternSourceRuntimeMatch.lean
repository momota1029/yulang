import Yulang.CommonPatternSourceRuntimeEnvironment
import Yulang.CommonPatternConcreteCaseTotal

/-! Real successful source matches discharge the concrete-value part of the
shared finite environment formula. The match equality, actual typed prefix
and captured logical environment are explicit. No arbitrary default is
assumed terminating; the actual finite data callback is used. -/

namespace Yulang.CommonPatternSourceRuntimeMatch

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration
open CommonPatternEnvironment
open CommonPatternTyping (bindingTypes valueAt)
open CommonPatternSourceElaboration (DefaultTyped)
open CommonPatternDataSafety (EnvironmentHolds)
open CommonPatternConcreteCaseSafety (defaults defaults_invariant)
open CommonPatternBindingAlignment (reorder)
open CasePatterns (Pattern)
open CaseValues (Bindings BindingsHold)

/-- Every prescribed source binding type list, arbitrary captured instances,
typed actual prefix, typed subject and actual returned bindings. Canonical
reordering preserves literal payloads, including reversed/nested or branches. -/
theorem actual_returns_typed (outer : EnvironmentHolds outerNames environment actualOuter)
    (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (typed : CommonAlignedPatternTyping.Typing (DefaultTyped outerNames environment) prior pattern input bindings)
    (actualPrefix : Bindings Empty) (prefixTyped : BindingsHold (bindingTypes prior) actualPrefix)
    (floatCheck : Empty → Empty → Bool) (subject : CommonData.Value) (subjectTyped : valueAt input subject)
    (returned : Bindings Empty)
    (matched : (ScopedCasePatterns.run floatCheck CaseDataTerms.defaultEval (actualPrefix ++ actualOuter) pattern subject).result =
      .ok (some returned)) :
    BindingsHold (bindingTypes bindings) (reorder pattern.names returned) := by
  have captured := CommonPatternCapturedEvaluation.run_capture floatCheck CaseDataTerms.defaultEval actualOuter pattern actualPrefix subject
  have captureSame : CommonPatternCapturedEvaluation.capture CaseDataTerms.defaultEval actualOuter = defaults actualOuter := rfl
  rw [captureSame] at captured
  rw [captured] at matched
  have equivalent := CommonPatternAlignedMatcher.run_equivalent floatCheck (defaults actualOuter) (defaults_invariant actualOuter)
    pattern typed.1 actualPrefix actualPrefix (fun _ => rfl) subject
  have relation := equivalent.2
  rw [matched] at relation
  have safe := CommonAlignedPatternSafeDefaults.typing_matches floatCheck (defaults actualOuter)
    (CommonPatternConcreteCaseTotal.default_sound outer) typed.2 typed.1 actualPrefix prefixTyped subject subjectTyped
  cases observed : (CommonPatternAlignedMatcher.run floatCheck (defaults actualOuter) actualPrefix pattern subject).result with
  | error => rw [observed] at relation; cases relation
  | ok option =>
      rw [observed] at relation safe
      cases option with
      | none => cases relation with | ok impossible => cases impossible
      | some canonical =>
          cases relation with
          | ok related =>
              cases related with
              | hit same =>
                  have names : (bindingTypes bindings).map Prod.fst = pattern.names := by
                    simpa only [bindingTypes, List.map_map, Function.comp_def] using typed.2.binding_names.symm
                  have distinct := CommonPatternMatchPaths.source_names_nodup pattern typed.1
                  have typeSelf : reorder pattern.names (bindingTypes bindings) = bindingTypes bindings := by
                    rw [← names]
                    exact CommonPatternBindingAlignment.reorder_self _ (by rw [names]; exact distinct)
                  have actual := CommonPatternBindingAlignment.reorder_bindings_hold pattern.names safe
                  rw [typeSelf, CommonPatternBindingAlignment.reorder_congr pattern.names canonical returned (fun name _ => same name)] at actual
                  exact actual

/-- At an actual successful source match, no runtime-value compatibility is
left as an extra model predicate: it is discharged by source typing and the
concrete evaluator, inside one shared allocation. This remains the structural
Common/source-data stage; full presence/carrier/effect contracts are separate. -/
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
      (CommonPatternSourceRuntimeEnvironment.generateEnvironment outerNames symbolic prior pattern input subject returned).Holds Common.model ρ := by
  rw [CommonPatternSourceElaboration.generateSourcePattern_exact pattern outerNames ρ symbolic environment semantic
    coreRelated symbolicRelated prior input,
    CommonPatternSourceRuntimeEnvironment.generateEnvironment_exact pattern outerNames ρ symbolic environment semantic
      coreRelated symbolicRelated prior input subject returned]
  constructor
  · rintro ⟨bindings, typed⟩
    exact ⟨bindings, typed, subjectTyped,
      actual_returns_typed outer pattern typed actualPrefix prefixTyped floatCheck subject subjectTyped returned matched⟩
  · rintro ⟨bindings, typed, subjectTyped, returnedTyped⟩
    exact ⟨bindings, typed⟩

end Yulang.CommonPatternSourceRuntimeMatch
