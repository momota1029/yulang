import Yulang.CommonAlignedPatternTyping
import Yulang.CommonPatternAlignedMatcher
import Yulang.CommonPatternPartialSafety

/-! Successful aligned matches carry the canonical Common binding types.
Errors are admitted under the same successful-default-only contract. -/

namespace Yulang.CommonAlignedPatternPartialSafety

open CommonPatternTyping (valueAt bindingTypes bindingTypes_append)
open CommonAlignedPatternTyping (RawTyping)
open CommonPatternLookup
open CommonPatternEnvironment (NamedTypes)
open Core.CommonData (Value)
open EvaluationTrace (Logged)
open CommonPatternPartialSafety (PartialHolds DefaultPartialSound)
open CommonPatternBindingAlignment (reorder)

theorem bindingTypes_reorder (names : List Nat) (bindings : NamedTypes) :
    bindingTypes (reorder names bindings) = reorder names (bindingTypes bindings) :=
  (CommonPatternBindingAlignment.reorder_mapValues valueAt names bindings).symm

theorem partial_alignResult (names : List Nat) (observed : CasePatterns.Observation Empty E R)
    (valid : PartialHolds types observed.result) :
    PartialHolds (reorder names types)
      (CommonPatternAlignedObservations.alignResult names observed).result := by
  cases observed with
  | mk trace result =>
      cases result with
      | error => trivial
      | ok option =>
          cases option with
          | none => trivial
          | some values =>
              change CaseValues.BindingsHold (bindingTypes (reorder names types)) (reorder names values)
              rw [bindingTypes_reorder]
              exact CommonPatternBindingAlignment.reorder_bindings_hold names valid

private theorem andThen_partial (first : CasePatterns.Observation Empty E R)
    (last : CaseValues.Bindings Empty → CasePatterns.Observation Empty E R)
    (firstValid : PartialHolds left first.result)
    (lastValid : ∀ prior, CaseValues.BindingsHold (bindingTypes left) prior →
      PartialHolds right (last prior).result) :
    PartialHolds (left ++ right) (ScopedCasePatterns.andThen first last).result := by
  simp only [ScopedCasePatterns.andThen, Logged.bind_result]
  cases observed : first.result with
  | error error => trivial
  | ok option =>
    rw [observed] at firstValid
    cases option with
    | none => trivial
    | some prior =>
      have rest := lastValid prior firstValid
      simp only [Except.bind, Logged.bind_result]
      cases later : (last prior).result with
      | error error => trivial
      | ok option =>
        rw [later] at rest
        cases option with
        | none => trivial
        | some more =>
          exact (by simpa only [PartialHolds, CasePatterns.success, Logged.ofResult,
            bindingTypes_append] using firstValid.append rest)

/-- Every default code, error/event type, actual outer environment and actual
subject. A successful result has exactly the declared ordered binding types.
Neither success nor failure is assumed in the conclusion. -/
theorem typing_matches_partial (floatCheck : Empty → Empty → Bool)
    (defaultEval : CaseValues.Bindings Empty → D → Logged E R Value)
    (defaults : DefaultPartialSound DefaultTyped defaultEval)
    (typed : RawTyping DefaultTyped types pattern input bindings) :
    PatternBindingChecks.NamesValid pattern →
    ∀ environment, CaseValues.BindingsHold (bindingTypes types) environment →
      ∀ value, valueAt input value →
        PartialHolds bindings
          (CommonPatternAlignedMatcher.run floatCheck defaultEval environment pattern value).result := by
  induction typed with
  | wildcard => intro sourceValid environment valid value valueValid; exact .nil
  | bind => intro sourceValid environment valid value valueValid; exact .cons valueValid .nil
  | literal admissible =>
      intro sourceValid environment valid value valueValid
      cases value <;> simp only [CommonPatternAlignedMatcher.run]
      all_goals first
        | (split <;> simp [CasePatterns.success, CasePatterns.miss, Logged.ofResult,
            PartialHolds, bindingTypes, CaseValues.BindingsHold.nil])
        | (exact True.intro)
  | intRange admissible bound =>
      intro sourceValid environment valid value valueValid
      cases value <;> simp only [CommonPatternAlignedMatcher.run]
      all_goals first
        | (split <;> simp [CasePatterns.success, CasePatterns.miss, Logged.ofResult,
            PartialHolds, bindingTypes, CaseValues.BindingsHold.nil])
        | (exact True.intro)
  | pair left right leftIH rightIH =>
      intro sourceValid environment valid value valueValid
      cases sourceValid with | pair vp vq apart =>
        obtain ⟨first, last, rfl, firstValid, lastValid⟩ :=
          pair_components valueValid _ _ (Common.subtype_refl _)
        simp only [CommonPatternAlignedMatcher.run]
        refine andThen_partial _ _ (leftIH vp environment valid first firstValid) ?_
        intro prior priorValid
        exact rightIH vq (prior ++ environment)
          (by simpa only [bindingTypes_append] using priorValid.append valid) last lastValid
  | recordEnd =>
      intro sourceValid environment valid value valueValid
      obtain ⟨fields, rfl⟩ := records_of_width valueValid (Common.subtype_refl _)
      exact .nil
  | field admissible child rest childIH restIH =>
      intro sourceValid environment valid value valueValid
      cases sourceValid with | field vp vr apart =>
        have width := Common.subtype_trans admissible
          ((CommonRecordTargetProfiles.subtype_emptyRecord_iff _).mpr rfl)
        obtain ⟨fields, rfl⟩ := records_of_width valueValid width
        obtain ⟨item, found, itemValid⟩ := required_lookup fields _ _ _ valueValid admissible
        simp only [CommonPatternAlignedMatcher.run, found]
        refine andThen_partial _ _ (childIH vp environment valid item itemValid) ?_
        intro prior priorValid
        exact restIH vr (prior ++ environment)
          (by simpa only [bindingTypes_append] using priorValid.append valid) (.record fields) valueValid
  | @defaultField name input payload types fallback fallbackType p left rest right
      optional fallbackTyped child restTyped childIH restIH =>
      intro sourceValid environment valid value valueValid
      cases sourceValid with | defaultField vp vr apart =>
        have width := (CommonRecordTargetProfiles.subtype_emptyRecord_iff input).mpr
          (CommonOptionalBound.optional_payload_shape name input payload optional)
        obtain ⟨fields, rfl⟩ := records_of_width valueValid width
        cases found : CaseValues.lookup name fields with
        | some item =>
          have itemValid := optional_lookup fields _ name payload item valueValid optional found
          rw [CommonPatternAlignedMatcher.default_present _ _ _ _ _ _ _ _ _ found]
          refine andThen_partial _ _ (childIH vp environment valid item ?_) ?_
          · exact typing_change_result itemValid _ (CommonBoundCoalescing.le_union_left _ _)
          · intro prior priorValid
            exact restIH vr (prior ++ environment)
              (by simpa only [bindingTypes_append] using priorValid.append valid)
              (.record fields) valueValid
        | none =>
          rw [CommonPatternAlignedMatcher.default_absent _ _ _ _ _ _ _ _ found, Logged.bind_result]
          cases evaluated : (defaultEval environment fallback).result with
          | error error => trivial
          | ok item =>
            have itemValid := defaults types fallback fallbackType fallbackTyped environment valid item evaluated
            refine andThen_partial _ _ (childIH vp environment valid item ?_) ?_
            · exact typing_change_result itemValid _ (CommonBoundCoalescing.le_union_right _ _)
            · intro prior priorValid
              exact restIH vr (prior ++ environment)
                (by simpa only [bindingTypes_append] using priorValid.append valid)
                (.record fields) valueValid
  | variant child childIH =>
      intro sourceValid environment valid value valueValid
      cases sourceValid with | variant vp =>
        obtain ⟨item, rfl, itemValid⟩ := variant_payload valueValid _ _ (Common.subtype_refl _)
        simpa [CommonPatternAlignedMatcher.run] using childIH vp environment valid item itemValid
  | @or types p input bindings q left right leftIH rightIH =>
      intro sourceValid environment valid value valueValid
      cases sourceValid with | or vp vq names =>
        have first := leftIH vp environment valid value valueValid
        have bindingNames := left.binding_names.symm
        have distinct := CommonPatternMatchPaths.source_names_nodup p vp
        have self : reorder p.names bindings = bindings := by
          rw [← bindingNames]
          exact CommonPatternBindingAlignment.reorder_self bindings (bindingNames ▸ distinct)
        have roundtrip : reorder p.names (reorder q.names bindings) = bindings :=
          CommonPatternBindingAlignment.reorder_roundtrip p.names q.names bindings bindingNames distinct
            (fun name member => (names name).mp member)
        simp only [CommonPatternAlignedMatcher.run, CommonPatternAlignedObservations.alignResult, Logged.bind_result]
        cases observed : (CommonPatternAlignedMatcher.run floatCheck defaultEval environment p value).result with
        | error error => trivial
        | ok option =>
            rw [observed] at first
            cases option with
            | none =>
                have aligned := partial_alignResult p.names
                  (CommonPatternAlignedMatcher.run floatCheck defaultEval environment q value)
                  (rightIH vq environment valid value valueValid)
                simpa only [roundtrip, CommonPatternAlignedObservations.alignResult, Except.bind] using aligned
            | some values =>
                have aligned := partial_alignResult p.names
                  (CasePatterns.success (E := E) (R := R) values) first
                simpa only [self, CommonPatternAlignedObservations.alignResult, Except.bind] using aligned
  | as child childIH =>
      intro sourceValid environment valid value valueValid
      cases sourceValid with | as vp fresh =>
        have matched := childIH vp environment valid value valueValid
        simp only [CommonPatternAlignedMatcher.run, Logged.bind_result]
        cases observed : (CommonPatternAlignedMatcher.run floatCheck defaultEval environment _ value).result with
        | error error => trivial
        | ok option =>
          rw [observed] at matched
          cases option with
          | none => trivial
          | some values => exact CaseValues.BindingsHold.cons valueValid matched
  | narrow below child childIH =>
      intro sourceValid environment valid value valueValid
      exact childIH sourceValid environment valid value (typing_change_result valueValid _ below)

end Yulang.CommonAlignedPatternPartialSafety
