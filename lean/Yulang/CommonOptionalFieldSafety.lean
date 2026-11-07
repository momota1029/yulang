import Yulang.CommonOptionalField
import Yulang.CommonAlignedPatternPartialSafety

/-! Partial correctness of the separate optional-input field rule. Missing
fields really miss, present payloads retain their declared types, and Q4
defaults in later children see only bindings produced by successful earlier
children. This does not adopt that rule as source language semantics. -/

namespace Yulang.CommonOptionalFieldSafety

set_option backward.isDefEq.respectTransparency false

open CommonPatternTyping (valueAt bindingTypes bindingTypes_append)
open CommonPatternEnvironment (NamedTypes)
open CommonPatternPartialSafety (PartialHolds DefaultPartialSound)
open CommonPatternLookup
open CommonOptionalField (Typing)
open Core.CommonData (Value)
open CaseValues (Bindings BindingsHold)
open EvaluationTrace (Logged)
open CommonPatternBindingAlignment (reorder)

private theorem andThen_partial (first : CasePatterns.Observation Empty E R)
    (last : Bindings Empty → CasePatterns.Observation Empty E R)
    (firstValid : PartialHolds left first.result)
    (lastValid : ∀ prior, BindingsHold (bindingTypes left) prior → PartialHolds right (last prior).result) :
    PartialHolds (left ++ right) (ScopedCasePatterns.andThen first last).result := by
  simp only [ScopedCasePatterns.andThen, Logged.bind_result]
  cases observed : first.result with
  | error => trivial
  | ok option =>
      rw [observed] at firstValid
      cases option with
      | none => trivial
      | some prior =>
          have tail := lastValid prior firstValid
          simp only [Except.bind, Logged.bind_result]
          cases later : (last prior).result with
          | error => trivial
          | ok option =>
              rw [later] at tail
              cases option with
              | none => trivial
              | some more =>
                  simpa only [PartialHolds, CasePatterns.success, Logged.ofResult, bindingTypes_append] using firstValid.append tail

theorem typing_matches_partial (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → Logged E R Value) (defaults : DefaultPartialSound DefaultTyped defaultEval)
    (typed : Typing DefaultTyped types name p rest input bindings)
    (sourceValid : PatternBindingChecks.NamesValid (.field name p rest))
    (environment : Bindings Empty) (environmentValid : BindingsHold (bindingTypes types) environment)
    (value : Value) (valid : valueAt input value) :
    PartialHolds bindings (CommonPatternAlignedMatcher.run floatCheck defaultEval environment (.field name p rest) value).result := by
  cases typed with
  | @field originalType payloadType left right below optional first last =>
      cases sourceValid with
      | field firstNames lastNames disjoint =>
          have original := typing_change_result valid (Core.PresenceGeneration.Comp.pure Common.model originalType) below
          have width := (CommonRecordTargetProfiles.subtype_emptyRecord_iff _).mpr
            (CommonOptionalBound.optional_payload_shape _ _ _ optional)
          obtain ⟨fields, rfl⟩ := records_of_width original width
          cases found : CaseValues.lookup name fields with
          | none => simp [CommonPatternAlignedMatcher.run, found, PartialHolds, CasePatterns.miss, Logged.ofResult]
          | some item =>
              have itemValid := optional_lookup fields _ _ _ item original optional found
              simp only [CommonPatternAlignedMatcher.run, found]
              refine andThen_partial _ _
                (CommonAlignedPatternPartialSafety.typing_matches_partial floatCheck defaultEval defaults first firstNames
                  environment environmentValid item itemValid) ?_
              intro prior priorValid
              exact CommonAlignedPatternPartialSafety.typing_matches_partial floatCheck defaultEval defaults last lastNames
                (prior ++ environment) (by simpa only [bindingTypes_append] using priorValid.append environmentValid) (.record fields) original

/-- The literal returned payloads of the original named matcher, in the
canonical source-name order, have exactly the prescribed shared binding
types. The existing name-invariance premise remains explicit. -/
theorem actual_returns_typed (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → Logged E R Value)
    (defaults : DefaultPartialSound DefaultTyped defaultEval)
    (invariant : CommonPatternAlignedMatcher.DefaultInvariant defaultEval)
    (typed : Typing DefaultTyped types name p rest input bindings)
    (sourceValid : PatternBindingChecks.NamesValid (.field name p rest))
    (environment : Bindings Empty) (environmentValid : BindingsHold (bindingTypes types) environment)
    (value : Value) (valid : valueAt input value) (returned : Bindings Empty)
    (matched : (ScopedCasePatterns.run floatCheck defaultEval environment (.field name p rest) value).result = .ok (some returned)) :
    BindingsHold (bindingTypes bindings) (reorder (.field name p rest : CasePatterns.Pattern Empty D).names returned) := by
  have equivalent := CommonPatternAlignedMatcher.run_equivalent floatCheck defaultEval invariant (.field name p rest) sourceValid
    environment environment (fun _ => rfl) value
  have relation := equivalent.2
  rw [matched] at relation
  have safe := typing_matches_partial floatCheck defaultEval defaults typed sourceValid environment environmentValid value valid
  cases observed : (CommonPatternAlignedMatcher.run floatCheck defaultEval environment (.field name p rest) value).result with
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
                  have names : (bindingTypes bindings).map Prod.fst = (.field name p rest : CasePatterns.Pattern Empty D).names := by
                    simpa only [bindingTypes, List.map_map, Function.comp_def, CasePatterns.Pattern.names] using typed.binding_names.symm
                  have distinct := CommonPatternMatchPaths.source_names_nodup (.field name p rest) sourceValid
                  have typeSelf : reorder (.field name p rest : CasePatterns.Pattern Empty D).names (bindingTypes bindings) = bindingTypes bindings := by
                    rw [← names]
                    exact CommonPatternBindingAlignment.reorder_self _ (by rw [names]; exact distinct)
                  have actual := CommonPatternBindingAlignment.reorder_bindings_hold (.field name p rest : CasePatterns.Pattern Empty D).names safe
                  rw [typeSelf, CommonPatternBindingAlignment.reorder_congr _ canonical returned (fun name _ => same name)] at actual
                  exact actual

end Yulang.CommonOptionalFieldSafety
