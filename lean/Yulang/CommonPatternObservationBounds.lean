import Yulang.CommonCaseEffectPaths
import Yulang.CommonAlignedPatternPartialSafety

/-! Partial default observations compose through the real ordered matcher.
The explicit callback contract permits arbitrary declared errors and traces;
it does not require a default to succeed. A shared row cap bounds every
default in a derivation. This is a conservative bound theorem, not a choice
of the source case's principal effect row. -/

namespace Yulang.CommonPatternObservationBounds

open CommonPatternTyping (valueAt bindingTypes bindingTypes_append)
open CommonAlignedPatternTyping (RawTyping)
open CommonPatternLookup
open CommonPatternEnvironment (NamedTypes)
open CommonPatternPartialSafety (DefaultPartialSound PartialHolds)
open CommonCaseEffectPaths (observationRow traceRow resultRow traceRow_append)
open EvaluationTrace (Logged)
open CaseEvaluation (Event)
open Core.CommonData (Value)

theorem pure_bound (source : E → Common.Row) (failure : R → Common.Row) (value : A) (cap : Common.Row) :
    Common.rowLe (observationRow source failure (Logged.ofResult (.ok value))) cap := by
  intro occurrence present
  rcases present with impossible | impossible <;> exact False.elim impossible

theorem bind_bound (source : E → Common.Row) (failure : R → Common.Row)
    (first : Logged (Event E) R A) (next : A → Logged (Event E) R B) (cap : Common.Row)
    (firstBound : Common.rowLe (observationRow source failure first) cap)
    (nextBound : ∀ value, first.result = .ok value → Common.rowLe (observationRow source failure (next value)) cap) :
    Common.rowLe (observationRow source failure (first.bind next)) cap := by
  cases first with
  | mk events result =>
      cases result with
      | error error => exact firstBound
      | ok value =>
          have later := nextBound value rfl
          intro occurrence present
          have flattened : traceRow source events occurrence ∨ observationRow source failure (next value) occurrence := by
            simpa [Logged.bind, Logged.prepend, observationRow, traceRow_append, resultRow,
              Common.rowJoin, Common.rowEmpty, or_assoc] using present
          rcases flattened with head | tail
          · exact firstBound occurrence (Or.inl head)
          · exact later occurrence tail

theorem andThen_bound (source : E → Common.Row) (failure : R → Common.Row)
    (first : CasePatterns.Observation Empty (Event E) R)
    (last : CaseValues.Bindings Empty → CasePatterns.Observation Empty (Event E) R)
    (left : NamedTypes) (cap : Common.Row) (valid : PartialHolds left first.result)
    (firstBound : Common.rowLe (observationRow source failure first) cap)
    (lastBound : ∀ prior, CaseValues.BindingsHold (bindingTypes left) prior →
      Common.rowLe (observationRow source failure (last prior)) cap) :
    Common.rowLe (observationRow source failure (ScopedCasePatterns.andThen first last)) cap := by
  apply bind_bound source failure first _ cap firstBound
  intro option observed
  cases option with
  | none => exact pure_bound source failure none cap
  | some prior =>
      have priorValid : CaseValues.BindingsHold (bindingTypes left) prior := by
        simpa only [observed, PartialHolds] using valid
      apply bind_bound source failure (last prior) _ cap (lastBound prior priorValid)
      intro result observed
      cases result with
      | none => exact pure_bound source failure none cap
      | some more => exact pure_bound source failure (some (prior ++ more)) cap

def DefaultObservationSound (source : E → Common.Row) (failure : R → Common.Row) (cap : Common.Row)
    (DefaultTyped : NamedTypes → D → Common.Ty → Prop)
    (defaultEval : CaseValues.Bindings Empty → D → Logged (Event E) R Value) : Prop :=
  DefaultPartialSound DefaultTyped defaultEval ∧
    ∀ types code type, DefaultTyped types code type → ∀ environment,
      CaseValues.BindingsHold (bindingTypes types) environment →
      Common.rowLe (observationRow source failure (defaultEval environment code)) cap

theorem align_bound (source : E → Common.Row) (failure : R → Common.Row)
    (names : List Nat) (observed : CasePatterns.Observation Empty (Event E) R) :
    observationRow source failure (CommonPatternAlignedObservations.alignResult names observed) =
      observationRow source failure observed := by
  cases observed with
  | mk events result => cases result <;> rfl

/-- Every structural derivation, every admitted real environment and subject,
including defaults that return declared errors. The callback contract is
explicit; no total-success or termination condition replaces it. -/
theorem typing_observation_bound (source : E → Common.Row) (failure : R → Common.Row) (cap : Common.Row)
    (floatCheck : Empty → Empty → Bool)
    (defaultEval : CaseValues.Bindings Empty → D → Logged (Event E) R Value)
    (defaults : DefaultObservationSound source failure cap DefaultTyped defaultEval)
    (typed : RawTyping DefaultTyped types pattern input bindings) :
    PatternBindingChecks.NamesValid pattern →
    ∀ environment, CaseValues.BindingsHold (bindingTypes types) environment →
      ∀ value, valueAt input value → Common.rowLe
        (observationRow source failure (CommonPatternAlignedMatcher.run floatCheck defaultEval environment pattern value)) cap := by
  induction typed with
  | wildcard => intro valid environment env value within; exact pure_bound source failure (some []) cap
  | bind => intro valid environment env value within; exact pure_bound source failure _ cap
  | literal admissible =>
      intro valid environment env value within
      cases value <;> simp only [CommonPatternAlignedMatcher.run]
      all_goals first
        | (split <;> exact pure_bound source failure _ cap)
        | exact pure_bound source failure _ cap
  | intRange admissible bounded =>
      intro valid environment env value within
      cases value <;> simp only [CommonPatternAlignedMatcher.run]
      all_goals first
        | (split <;> exact pure_bound source failure _ cap)
        | exact pure_bound source failure _ cap
  | pair left right ihl ihr =>
      intro valid environment env value within
      cases valid with | pair vp vq apart =>
        obtain ⟨first, last, rfl, firstValid, lastValid⟩ := pair_components within _ _ (Common.subtype_refl _)
        simp only [CommonPatternAlignedMatcher.run]
        refine andThen_bound source failure _ _ _ cap
          (CommonAlignedPatternPartialSafety.typing_matches_partial floatCheck defaultEval defaults.1 left vp environment env first firstValid)
          (ihl vp environment env first firstValid) ?_
        intro prior priorValid
        exact ihr vq (prior ++ environment)
          (by simpa only [bindingTypes_append] using priorValid.append env) last lastValid
  | recordEnd =>
      intro valid environment env value within
      obtain ⟨fields, rfl⟩ := records_of_width within (Common.subtype_refl _)
      exact pure_bound source failure (some []) cap
  | field below child rest ihc ihr =>
      intro valid environment env value within
      cases valid with | field vp vr apart =>
        have width := Common.subtype_trans below ((CommonRecordTargetProfiles.subtype_emptyRecord_iff _).mpr rfl)
        obtain ⟨fields, rfl⟩ := records_of_width within width
        obtain ⟨item, found, itemValid⟩ := required_lookup fields _ _ _ within below
        simp only [CommonPatternAlignedMatcher.run, found]
        refine andThen_bound source failure _ _ _ cap
          (CommonAlignedPatternPartialSafety.typing_matches_partial floatCheck defaultEval defaults.1 child vp environment env item itemValid)
          (ihc vp environment env item itemValid) ?_
        intro prior priorValid
        exact ihr vr (prior ++ environment)
          (by simpa only [bindingTypes_append] using priorValid.append env) (.record fields) within
  | @defaultField name input payload types fallback fallbackType p left rest right optional fallbackTyped child restTyped ihc ihr =>
      intro valid environment env value within
      cases valid with | defaultField vp vr apart =>
        have width := (CommonRecordTargetProfiles.subtype_emptyRecord_iff input).mpr
          (CommonOptionalBound.optional_payload_shape name input payload optional)
        obtain ⟨fields, rfl⟩ := records_of_width within width
        have children (item : Value) (itemValid : valueAt (.union payload fallbackType) item) :=
          andThen_bound source failure
            (CommonPatternAlignedMatcher.run floatCheck defaultEval environment p item)
            (fun prior => CommonPatternAlignedMatcher.run floatCheck defaultEval (prior ++ environment) rest (.record fields))
            left cap
            (CommonAlignedPatternPartialSafety.typing_matches_partial floatCheck defaultEval defaults.1 child vp environment env item itemValid)
            (ihc vp environment env item itemValid)
            (fun prior priorValid => ihr vr (prior ++ environment)
              (by simpa only [bindingTypes_append] using priorValid.append env) (.record fields) within)
        cases found : CaseValues.lookup name fields with
        | some item =>
            rw [CommonPatternAlignedMatcher.default_present _ _ _ _ _ _ _ _ _ found]
            exact children item (typing_change_result (optional_lookup fields _ name payload item within optional found) _
              (CommonBoundCoalescing.le_union_left _ _))
        | none =>
            rw [CommonPatternAlignedMatcher.default_absent _ _ _ _ _ _ _ _ found]
            apply bind_bound source failure _ _ cap (defaults.2 types fallback fallbackType fallbackTyped environment env)
            intro item evaluated
            exact children item (typing_change_result
              (defaults.1 types fallback fallbackType fallbackTyped environment env item evaluated) _
              (CommonBoundCoalescing.le_union_right _ _))
  | variant child ih =>
      intro valid environment env value within
      cases valid with | variant vp =>
        obtain ⟨item, rfl, itemValid⟩ := variant_payload within _ _ (Common.subtype_refl _)
        simpa [CommonPatternAlignedMatcher.run] using ih vp environment env item itemValid
  | @or types p input bindings q left right ihl ihr =>
      intro valid environment env value within
      cases valid with | or vp vq names =>
        simp only [CommonPatternAlignedMatcher.run, align_bound]
        apply bind_bound source failure _ _ cap (ihl vp environment env value within)
        intro option observed
        cases option with
        | none => exact ihr vq environment env value within
        | some values => exact pure_bound source failure (some values) cap
  | as child ih =>
      intro valid environment env value within
      cases valid with | as vp fresh =>
        simp only [CommonPatternAlignedMatcher.run]
        apply bind_bound source failure _ _ cap (ih vp environment env value within)
        intro option observed
        cases option <;> exact pure_bound source failure _ cap
  | narrow below child ih =>
      intro valid environment env value within
      exact ih valid environment env value (typing_change_result within _ below)

theorem typing_partial_and_bound (source : E → Common.Row) (failure : R → Common.Row) (cap : Common.Row)
    (floatCheck : Empty → Empty → Bool)
    (defaultEval : CaseValues.Bindings Empty → D → Logged (Event E) R Value)
    (defaults : DefaultObservationSound source failure cap DefaultTyped defaultEval)
    (typed : CommonAlignedPatternTyping.Typing DefaultTyped types pattern input bindings)
    (environment : CaseValues.Bindings Empty) (env : CaseValues.BindingsHold (bindingTypes types) environment)
    (value : Value) (within : valueAt input value) :
    PartialHolds bindings (CommonPatternAlignedMatcher.run floatCheck defaultEval environment pattern value).result ∧
      Common.rowLe (observationRow source failure (CommonPatternAlignedMatcher.run floatCheck defaultEval environment pattern value)) cap :=
  ⟨CommonAlignedPatternPartialSafety.typing_matches_partial floatCheck defaultEval defaults.1 typed.2 typed.1 environment env value within,
    typing_observation_bound source failure cap floatCheck defaultEval defaults typed.2 typed.1 environment env value within⟩

theorem related_observation_rows (source : E → Common.Row) (failure : R → Common.Row)
    (first : Logged (Event E) R A) (last : Logged (Event E) R B)
    (same : CommonPatternAlignedObservations.LoggedRel relation first last) :
    observationRow source failure first = observationRow source failure last := by
  rcases first with ⟨firstEvents, firstResult⟩
  rcases last with ⟨lastEvents, lastResult⟩
  rcases same with ⟨events, results⟩
  change firstEvents = lastEvents at events
  subst lastEvents
  cases results <;> rfl

/-- The unmodified source matcher has the same complete observation bound.
Only the existing name-invariance contract is used to pass nested or exits. -/
theorem actual_typing_observation_bound (source : E → Common.Row) (failure : R → Common.Row) (cap : Common.Row)
    (floatCheck : Empty → Empty → Bool)
    (defaultEval : CaseValues.Bindings Empty → D → Logged (Event E) R Value)
    (invariant : CommonPatternAlignedMatcher.DefaultInvariant defaultEval)
    (defaults : DefaultObservationSound source failure cap DefaultTyped defaultEval)
    (typed : CommonAlignedPatternTyping.Typing DefaultTyped types pattern input bindings)
    (environment : CaseValues.Bindings Empty) (env : CaseValues.BindingsHold (bindingTypes types) environment)
    (value : Value) (within : valueAt input value) :
    Common.rowLe (observationRow source failure (ScopedCasePatterns.run floatCheck defaultEval environment pattern value)) cap := by
  have equivalent := CommonPatternAlignedMatcher.run_equivalent floatCheck defaultEval invariant pattern typed.1
    environment environment (fun _ => rfl) value
  rw [← related_observation_rows source failure _ _ equivalent]
  exact typing_observation_bound source failure cap floatCheck defaultEval defaults typed.2 typed.1 environment env value within

end Yulang.CommonPatternObservationBounds
