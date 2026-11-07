import Yulang.CommonPatternLookup
import Yulang.CommonPatternEnvironment
import Yulang.ScopedCasePatternSafety

/-!
# Independent Common rules for structural patterns and their actual matches

This auxiliary judgment uses Common producer types and the existing source
pattern syntax. Its rules do not mention formulas, inference, or a solver.
The scoped matcher is left unchanged. Nominal/list patterns, multi-tag variant
rows, float values, source presence-annotation validation and ordered case
coverage remain outside this intermediate judgment; it is not the full B2
`common_pattern_environment_exact` statement.

Bindings are pure and monomorphic. The remainder of a record pattern consumes
the original record, and a later component receives `prior ++ environment`.
Default input is the union of the optional payload and the fallback value type.
Its runtime contract is explicit and is not inferred from an effect row here.
-/

namespace Yulang.CommonPatternTyping

open Core.CommonData (Value ValueTyping)
open Core.PresenceGeneration (Comp)
open CasePatterns (Pattern Holds)
open EvaluationTrace (Logged)
open CommonPatternEnvironment (NamedTypes)
open CommonPatternLookup
open CommonDefaultRequired (OptionalPayload)

/-- This is a readout from the independent constructor value judgment, not an
identification of Common type equivalence with equality of runtime sets. -/
def valueAt (type : Common.Ty) : CaseValues.Ty Empty :=
  fun value => ValueTyping Common.model value (Comp.pure Common.model type)

def bindingTypes (types : NamedTypes) : List (Nat × CaseValues.Ty Empty) :=
  types.map fun binding => (binding.1, valueAt binding.2)

@[simp] theorem bindingTypes_append (first last : NamedTypes) :
    bindingTypes (first ++ last) = bindingTypes first ++ bindingTypes last := by
  simp [bindingTypes]

/-- Defaults are checked in all actual environments admitted by their Common
binding types. Effects and rejected executions require a separate row bridge;
this local soundness contract describes successful terminating defaults. -/
def DefaultSound (DefaultTyped : NamedTypes → D → Common.Ty → Prop)
    (defaultEval : CaseValues.Bindings Empty → D → Logged E R Value) : Prop :=
  ∀ types code type, DefaultTyped types code type →
    ∀ environment, CaseValues.BindingsHold (bindingTypes types) environment →
      ∃ value, (defaultEval environment code).result = .ok value ∧ valueAt type value

/-- Structural pattern rules over the actual Common carrier. No constructor
below is an alias for a constraint formula or a successful matcher result. -/
inductive Typing (DefaultTyped : NamedTypes → D → Common.Ty → Prop) :
    NamedTypes → Pattern Empty D → Common.Ty → NamedTypes → Prop where
  | wildcard : Typing DefaultTyped types .wildcard input []
  | bind : Typing DefaultTyped types (.bind name) input [(name, input)]
  | literal : Common.Subtype input (.base (Core.CommonData.literalBase expected)) →
      Typing DefaultTyped types (.literal expected) input []
  | intRange : Common.Subtype input (.base .int) → lower.isSome ∨ upper.isSome →
      Typing DefaultTyped types (.intRange lower upper) input []
  | pair : Typing DefaultTyped types p a left →
      Typing DefaultTyped (left ++ types) q b right →
      Typing DefaultTyped types (.pair p q) (Common.pair a b) (left ++ right)
  | recordEnd : Typing DefaultTyped types .recordEnd Common.emptyRecord []
  | field : Common.Subtype input (Common.required name payload) →
      Typing DefaultTyped types p payload left →
      Typing DefaultTyped (left ++ types) rest input right →
      Typing DefaultTyped types (.field name p rest) input (left ++ right)
  | defaultField : OptionalPayload name input payload →
      DefaultTyped types fallback fallbackType →
      Typing DefaultTyped types p (.union payload fallbackType) left →
      Typing DefaultTyped (left ++ types) rest input right →
      Typing DefaultTyped types (.defaultField name fallback p rest) input (left ++ right)
  | variant : Typing DefaultTyped types p payload bindings →
      Typing DefaultTyped types (.variant tag p) (Common.variant tag payload) bindings
  | or : Typing DefaultTyped types p input bindings →
      Typing DefaultTyped types q input bindings →
      Typing DefaultTyped types (.or p q) input bindings
  | as : Typing DefaultTyped types p input bindings →
      Typing DefaultTyped types (.as p name) input ((name, input) :: bindings)
  | narrow : Common.Subtype input original →
      Typing DefaultTyped types p original bindings →
      Typing DefaultTyped types p input bindings

/-- Source traversal order is retained exactly, including the outer `as`
binder before its child. The two or alternatives share the same output list. -/
theorem Typing.binding_names (typed : Typing DefaultTyped types pattern input bindings) :
    pattern.names = bindings.map Prod.fst := by
  induction typed <;> simp_all [Pattern.names]

/-- The actual scoped matcher preserves all declared Common binding types.
The premise on default evaluation quantifies over every admitted accumulated
environment. A refutable pattern may miss; success is not assumed, and an
error is excluded only by that explicit default-evaluation contract. -/
theorem typing_matches (floatCheck : Empty → Empty → Bool)
    (defaultEval : CaseValues.Bindings Empty → D → Logged E R Value)
    (defaults : DefaultSound DefaultTyped defaultEval)
    (typed : Typing DefaultTyped types pattern input bindings) :
    ∀ environment, CaseValues.BindingsHold (bindingTypes types) environment →
      ∀ value, valueAt input value →
        Holds (bindingTypes bindings)
          (ScopedCasePatterns.run floatCheck defaultEval environment pattern value).result := by
  induction typed with
  | wildcard => intro environment valid value valueValid; exact .nil
  | bind => intro environment valid value valueValid; exact .cons valueValid .nil
  | literal admissible =>
      intro environment valid value valueValid
      cases value <;> simp only [ScopedCasePatterns.run]
      all_goals first
        | (split <;> simp [CasePatterns.success, CasePatterns.miss, Logged.ofResult,
            Holds, bindingTypes, CaseValues.BindingsHold.nil])
        | (exact True.intro)
  | intRange admissible bound =>
      intro environment valid value valueValid
      cases value <;> simp only [ScopedCasePatterns.run]
      all_goals first
        | (split <;> simp [CasePatterns.success, CasePatterns.miss, Logged.ofResult,
            Holds, bindingTypes, CaseValues.BindingsHold.nil])
        | (exact True.intro)
  | pair left right leftIH rightIH =>
      intro environment valid value valueValid
      obtain ⟨first, last, rfl, firstValid, lastValid⟩ :=
        pair_components valueValid _ _ (Common.subtype_refl _)
      simp only [ScopedCasePatterns.run, bindingTypes_append]
      refine ScopedCasePatterns.andThen_holds _ _ (leftIH environment valid first firstValid) ?_
      intro prior priorValid
      exact rightIH (prior ++ environment)
        (by simpa only [bindingTypes_append] using priorValid.append valid) last lastValid
  | recordEnd =>
      intro environment valid value valueValid
      obtain ⟨fields, rfl⟩ := records_of_width valueValid (Common.subtype_refl _)
      exact .nil
  | field admissible child rest childIH restIH =>
      intro environment valid value valueValid
      have width := Common.subtype_trans admissible
        ((CommonRecordTargetProfiles.subtype_emptyRecord_iff _).mpr rfl)
      obtain ⟨fields, rfl⟩ := records_of_width valueValid width
      obtain ⟨item, found, itemValid⟩ := required_lookup fields _ _ _ valueValid admissible
      simp only [ScopedCasePatterns.run, found, bindingTypes_append]
      refine ScopedCasePatterns.andThen_holds _ _ (childIH environment valid item itemValid) ?_
      intro prior priorValid
      exact restIH (prior ++ environment)
        (by simpa only [bindingTypes_append] using priorValid.append valid) (.record fields) valueValid
  | @defaultField name input payload types fallback fallbackType p left rest right
      optional fallbackTyped child restTyped childIH restIH =>
      intro environment valid value valueValid
      have width := (CommonRecordTargetProfiles.subtype_emptyRecord_iff input).mpr
        (CommonOptionalBound.optional_payload_shape name input payload optional)
      obtain ⟨fields, rfl⟩ := records_of_width valueValid width
      simp only [bindingTypes_append]
      cases found : CaseValues.lookup name fields with
      | some item =>
          have itemValid := optional_lookup fields _ name payload item valueValid optional found
          rw [ScopedCasePatterns.default_present _ _ _ _ _ _ _ _ _ found]
          refine ScopedCasePatterns.andThen_holds _ _ (childIH environment valid item ?_) ?_
          · exact typing_change_result itemValid _ (CommonBoundCoalescing.le_union_left _ _)
          · intro prior priorValid
            exact restIH (prior ++ environment)
              (by simpa only [bindingTypes_append] using priorValid.append valid)
              (.record fields) valueValid
      | none =>
          obtain ⟨item, evaluated, itemValid⟩ :=
            defaults types fallback fallbackType fallbackTyped environment valid
          rw [ScopedCasePatterns.default_absent _ _ _ _ _ _ _ _ found,
            Logged.bind_result, evaluated]
          refine ScopedCasePatterns.andThen_holds _ _ (childIH environment valid item ?_) ?_
          · exact typing_change_result itemValid _ (CommonBoundCoalescing.le_union_right _ _)
          · intro prior priorValid
            exact restIH (prior ++ environment)
              (by simpa only [bindingTypes_append] using priorValid.append valid)
              (.record fields) valueValid
  | variant child childIH =>
      intro environment valid value valueValid
      obtain ⟨item, rfl, itemValid⟩ := variant_payload valueValid _ _ (Common.subtype_refl _)
      simpa [ScopedCasePatterns.run] using childIH environment valid item itemValid
  | or left right leftIH rightIH =>
      intro environment valid value valueValid
      have first := leftIH environment valid value valueValid
      simp only [ScopedCasePatterns.run, Logged.bind_result]
      cases observed : (ScopedCasePatterns.run floatCheck defaultEval environment _ value).result with
      | error error => rw [observed] at first; cases first
      | ok option =>
          rw [observed] at first
          cases option with
          | none => exact rightIH environment valid value valueValid
          | some values => exact first
  | as child childIH =>
      intro environment valid value valueValid
      have matched := childIH environment valid value valueValid
      simp only [ScopedCasePatterns.run, Logged.bind_result]
      cases observed : (ScopedCasePatterns.run floatCheck defaultEval environment _ value).result with
      | error error => rw [observed] at matched; cases matched
      | ok option =>
          rw [observed] at matched
          cases option with
          | none => trivial
          | some values => exact CaseValues.BindingsHold.cons valueValid matched
  | narrow below child childIH =>
      intro environment valid value valueValid
      exact childIH environment valid value (typing_change_result valueValid _ below)

end Yulang.CommonPatternTyping
