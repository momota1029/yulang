import Yulang.ScopedCasePatterns

/-!
# Safe pattern defaults in the accumulated lexical environment

The contract for default code quantifies over every matching type/value
environment. Pattern typing passes the bindings of each successful left
component to the right component's type environment. Matching success is not
assumed: a refutable pattern may miss, but cannot fail with a runtime error.
-/

namespace Yulang.ScopedCasePatterns

open CaseValues LiteralValues EvaluationTrace
open CasePatterns (Pattern Observation success miss Holds)

def DefaultSound (DefaultTyped : List (Nat × Ty F) → D → Ty F → Prop)
    (defaultEval : Bindings F → D → Logged E R (Value F)) : Prop :=
  ∀ types code type, DefaultTyped types code type →
    ∀ environment, BindingsHold types environment →
      ∃ value, (defaultEval environment code).result = .ok value ∧ type value

theorem Typing.binding_names (typed : Typing DefaultTyped types pattern input bindings) :
    pattern.names = bindings.map Prod.fst := by
  induction typed <;> simp_all [Pattern.names]

theorem Typing.aligned (typed : Typing DefaultTyped types pattern input bindings) :
    pattern.aligned = true := by
  induction typed with
  | wildcard | bind | literal | recordEnd | nil => rfl
  | @intRange input types lower upper _ valid =>
      cases lower <;> cases upper <;> simp_all [Pattern.aligned]
  | pair _ _ left right | field _ _ _ left right | defaultField _ _ _ _ left right
    | cons _ _ left right | snoc _ _ left right => simp [Pattern.aligned, left, right]
  | variant _ child | mergedVariant _ _ _ child | nominal _ child | mergedNominal _ _ _ child
    | as _ child => exact child
  | or left right leftIH rightIH =>
      simp only [Pattern.aligned, leftIH, rightIH, Bool.true_and]
      apply (CasePatterns.sameNames_exact _ _).mpr
      intro name
      rw [left.binding_names, right.binding_names]
  | narrow _ _ child => exact child

/-- A typed match either misses or returns bindings of the declared types;
it cannot produce an error. All default expressions use their actual scope. -/
theorem typing_matches (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F))
    (defaults : DefaultSound DefaultTyped defaultEval)
    (typed : Typing DefaultTyped types pattern input bindings) :
    ∀ (environment : Bindings F), BindingsHold types environment →
      ∀ (value : Value F), input value →
        Holds bindings (run floatCheck defaultEval environment pattern value).result := by
  induction typed with
  | wildcard => intro environment valid value valueValid; exact .nil
  | bind => intro environment valid value valueValid; exact .cons valueValid .nil
  | literal admissible =>
      intro environment valid value valueValid
      cases value <;> simp only [run]
      all_goals first
        | (split <;> simp [success, miss, Logged.ofResult, Holds, BindingsHold.nil])
        | (exact True.intro)
  | intRange admissible bound =>
      intro environment valid value valueValid
      cases value <;> simp only [run]
      all_goals first
        | (split <;> simp [success, miss, Logged.ofResult, Holds, BindingsHold.nil])
        | (exact True.intro)
  | pair left right leftIH rightIH =>
      intro environment valid value valueValid
      cases value with
      | pair first last =>
          exact andThen_holds _ _ (leftIH environment valid first valueValid.1)
            (fun prior priorValid => rightIH (prior ++ environment) (priorValid.append valid) last valueValid.2)
      | literal | record | variant | nominal | list => cases valueValid
  | recordEnd =>
      intro environment valid value valueValid
      cases value with
      | record fields => exact .nil
      | literal | pair | variant | nominal | list => cases valueValid
  | field admissible child rest childIH restIH =>
      intro environment valid value valueValid
      have fieldValid := admissible value valueValid
      cases value with
      | record fields =>
          obtain ⟨item, found, itemValid⟩ := fieldValid
          simp only [run, found]
          exact andThen_holds _ _ (childIH environment valid item itemValid)
            (fun prior priorValid => restIH (prior ++ environment) (priorValid.append valid)
              (.record fields) valueValid)
      | literal | pair | variant | nominal | list => cases fieldValid
  | @defaultField input name payload types fallback fallbackType p left rest right
      admissible fallbackTyped child restTyped childIH restIH =>
      intro environment valid value valueValid
      have optionalValid := admissible value valueValid
      cases value with
      | record fields =>
          cases found : lookup name fields with
          | some item =>
              rw [default_present _ _ _ _ _ _ _ _ _ found]
              exact andThen_holds _ _ (childIH environment valid item (Or.inl (optionalValid item found)))
                (fun prior priorValid => restIH (prior ++ environment) (priorValid.append valid)
                  (.record fields) valueValid)
          | none =>
              obtain ⟨item, evaluated, itemValid⟩ := defaults _ fallback fallbackType fallbackTyped environment valid
              rw [default_absent _ _ _ _ _ _ _ _ found, Logged.bind_result, evaluated]
              exact andThen_holds _ _ (childIH environment valid item (Or.inr itemValid))
                (fun prior priorValid => restIH (prior ++ environment) (priorValid.append valid)
                  (.record fields) valueValid)
      | literal | pair | variant | nominal | list => cases optionalValid
  | nil =>
      intro environment valid value valueValid
      cases value with
      | list values => cases values <;> first | exact BindingsHold.nil | exact True.intro
      | literal | pair | record | variant | nominal => cases valueValid
  | cons head rest headIH restIH =>
      intro environment valid value valueValid
      cases value with
      | list values =>
          cases values with
          | nil => trivial
          | cons first more =>
              exact andThen_holds _ _ (headIH environment valid first (valueValid first (by simp)))
                (fun prior priorValid => restIH (prior ++ environment) (priorValid.append valid)
                  (.list more) (fun item member => valueValid item (by simp [member])))
      | literal | pair | record | variant | nominal => cases valueValid
  | snoc init last initIH lastIH =>
      intro environment valid value valueValid
      cases value with
      | list values =>
          cases reversed : values.reverse with
          | nil => simp [run, reversed, miss, Logged.ofResult, Holds]
          | cons final earlier =>
              have original : values = earlier.reverse ++ [final] := by
                have same := congrArg List.reverse reversed
                simpa using same
              simp only [run, reversed]
              refine andThen_holds _ _ (initIH environment valid (.list earlier.reverse) ?_) ?_
              · intro item member
                apply valueValid item
                rw [original]
                simp [member]
              · intro prior priorValid
                apply lastIH (prior ++ environment) (priorValid.append valid) final
                apply valueValid final
                rw [original]
                simp
      | literal | pair | record | variant | nominal => cases valueValid
  | variant child childIH =>
      intro environment valid value valueValid
      cases value with
      | variant name payload =>
          obtain ⟨rfl, payloadValid⟩ := valueValid
          simpa [run] using childIH environment valid payload payloadValid
      | literal | pair | record | nominal | list => cases valueValid
  | @mergedVariant tag payload types p bindings row found child childIH =>
      intro environment valid value valueValid
      cases value with
      | variant name item =>
          by_cases same : tag = name
          · subst name
            obtain ⟨actual, actualFound, itemValid⟩ := valueValid
            have equal : actual = payload := Option.some.inj (actualFound.symm.trans found)
            subst actual
            simpa [run] using childIH environment valid item itemValid
          · simp [run, same, Holds, miss, Logged.ofResult]
      | literal | pair | record | nominal | list => cases valueValid
  | nominal child childIH =>
      intro environment valid value valueValid
      cases value with
      | nominal name ctor payload =>
          obtain ⟨rfl, rfl, payloadValid⟩ := valueValid
          simpa [run] using childIH environment valid payload payloadValid
      | literal | pair | record | variant | list => cases valueValid
  | @mergedNominal ctorId payload types p bindings typeId row found child childIH =>
      intro environment valid value valueValid
      cases value with
      | nominal typeName ctorName item =>
          obtain ⟨rfl, actual, actualFound, itemValid⟩ := valueValid
          by_cases same : ctorId = ctorName
          · subst ctorName
            have equal : actual = payload := Option.some.inj (actualFound.symm.trans found)
            subst actual
            simpa [run] using childIH environment valid item itemValid
          · simp [run, same, Holds, miss, Logged.ofResult]
      | literal | pair | record | variant | list => cases valueValid
  | or left right leftIH rightIH =>
      intro environment valid value valueValid
      have first := leftIH environment valid value valueValid
      simp only [run, Logged.bind_result]
      cases observed : (run floatCheck defaultEval environment _ value).result with
      | error error => rw [observed] at first; cases first
      | ok option =>
          rw [observed] at first
          cases option with
          | none => exact rightIH environment valid value valueValid
          | some values => exact first
  | as child childIH =>
      intro environment valid value valueValid
      have matched := childIH environment valid value valueValid
      simp only [run, Logged.bind_result]
      cases observed : (run floatCheck defaultEval environment _ value).result with
      | error error => rw [observed] at matched; cases matched
      | ok option =>
          rw [observed] at matched
          cases option with
          | none => trivial
          | some values => exact BindingsHold.cons valueValid matched
  | narrow below child childIH =>
      intro environment valid value valueValid
      exact childIH environment valid value (below value valueValid)

theorem typed_match_no_error (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F))
    (defaults : DefaultSound DefaultTyped defaultEval)
    (typed : Typing DefaultTyped types pattern input bindings)
    (environment : Bindings F) (valid : BindingsHold types environment)
    (value : Value F) (valueValid : input value) (error : R) :
    (run floatCheck defaultEval environment pattern value).result ≠ .error error := by
  intro failed
  have safe := typing_matches floatCheck defaultEval defaults typed environment valid value valueValid
  rw [failed] at safe
  exact safe

theorem typed_match_bindings (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F))
    (defaults : DefaultSound DefaultTyped defaultEval)
    (typed : Typing DefaultTyped types pattern input bindings)
    (environment : Bindings F) (valid : BindingsHold types environment)
    (value : Value F) (valueValid : input value) (matched : Bindings F)
    (successful : (run floatCheck defaultEval environment pattern value).result = .ok (some matched)) :
    BindingsHold bindings matched := by
  have safe := typing_matches floatCheck defaultEval defaults typed environment valid value valueValid
  simpa [successful, Holds] using safe

end Yulang.ScopedCasePatterns
