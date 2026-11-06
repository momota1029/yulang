import Yulang.ScopedCasePatternSafety

/-!
# Declarative irrefutability for scoped patterns

This judgement certifies an unguarded arm without evaluating a pattern or
sampling its input. It covers product, required/default record fields and
single variant/constructor shapes, together with wildcard, bindings, or and
as. General multi-arm coverage remains a separate responsibility.
-/

namespace Yulang.ScopedCasePatterns

open CaseValues EvaluationTrace
open CasePatterns (Pattern Observation success miss Holds)

@[local simp] private theorem except_bind_ok (value : A) (next : A → Except R B) :
    (Except.ok value).bind next = next value := rfl

inductive TotalTyping (DefaultTyped : List (Nat × Ty F) → D → Ty F → Prop) :
    List (Nat × Ty F) → Pattern F D → Ty F → List (Nat × Ty F) → Prop where
  | wildcard : TotalTyping DefaultTyped types .wildcard input []
  | bind : TotalTyping DefaultTyped types (.bind name) input [(name, input)]
  | pair : TotalTyping DefaultTyped types p a left →
      TotalTyping DefaultTyped (left ++ types) q b right →
      TotalTyping DefaultTyped types (.pair p q) (Ty.pair a b) (left ++ right)
  | recordEnd : TotalTyping DefaultTyped types .recordEnd Ty.records []
  | field : Ty.Le input (Ty.required name payload) →
      TotalTyping DefaultTyped types p payload left →
      TotalTyping DefaultTyped (left ++ types) rest input right →
      TotalTyping DefaultTyped types (.field name p rest) input (left ++ right)
  | defaultField : Ty.Le input (Ty.optional name payload) → DefaultTyped types fallback fallbackType →
      TotalTyping DefaultTyped types p (Ty.union payload fallbackType) left →
      TotalTyping DefaultTyped (left ++ types) rest input right →
      TotalTyping DefaultTyped types (.defaultField name fallback p rest) input (left ++ right)
  | variant : TotalTyping DefaultTyped types p payload bindings →
      TotalTyping DefaultTyped types (.variant tag p) (Ty.variant tag payload) bindings
  | nominal : TotalTyping DefaultTyped types p payload bindings →
      TotalTyping DefaultTyped types (.nominal typeId ctorId p) (Ty.nominal typeId ctorId payload) bindings
  | orLeft : TotalTyping DefaultTyped types p input bindings → Typing DefaultTyped types q input bindings →
      TotalTyping DefaultTyped types (.or p q) input bindings
  | orRight : Typing DefaultTyped types p input bindings → TotalTyping DefaultTyped types q input bindings →
      TotalTyping DefaultTyped types (.or p q) input bindings
  | as : TotalTyping DefaultTyped types p input bindings →
      TotalTyping DefaultTyped types (.as p name) input ((name, input) :: bindings)
  | narrow : Ty.Le input original → TotalTyping DefaultTyped types p original bindings →
      TotalTyping DefaultTyped types p input bindings

theorem TotalTyping.typing (total : TotalTyping DefaultTyped types pattern input bindings) :
    Typing DefaultTyped types pattern input bindings := by
  induction total with
  | wildcard => exact .wildcard
  | bind => exact .bind
  | pair _ _ left right => exact .pair left right
  | recordEnd => exact .recordEnd
  | field below _ _ left right => exact .field below left right
  | defaultField below code _ _ left right => exact .defaultField below code left right
  | variant _ child => exact .variant child
  | nominal _ child => exact .nominal child
  | orLeft _ right left => exact .or left right
  | orRight left _ right => exact .or left right
  | as _ child => exact .as child
  | narrow below _ child => exact .narrow below child

private theorem andThen_matches (first : Observation F E R) (last : Bindings F → Observation F E R)
    (a : ∃ values, first.result = .ok (some values) ∧ BindingsHold left values)
    (b : ∀ values, BindingsHold left values →
      ∃ more, (last values).result = .ok (some more) ∧ BindingsHold right more) :
    ∃ values, (andThen first last).result = .ok (some values) ∧ BindingsHold (left ++ right) values := by
  obtain ⟨values, firstEval, firstValid⟩ := a
  obtain ⟨more, lastEval, lastValid⟩ := b values firstValid
  exact ⟨values ++ more,
    by simp [andThen, Logged.bind_result, firstEval, lastEval, success, Logged.ofResult],
    firstValid.append lastValid⟩

/-- Every suitably typed value is matched, and every bound value has its
declared type. Default evaluation is justified in its accumulated scope. -/
theorem TotalTyping.matches (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F))
    (defaults : DefaultSound DefaultTyped defaultEval)
    (total : TotalTyping DefaultTyped types pattern input bindings) :
    ∀ (environment : Bindings F), BindingsHold types environment →
      ∀ (value : Value F), input value →
        ∃ matched, (run floatCheck defaultEval environment pattern value).result = .ok (some matched) ∧
          BindingsHold bindings matched := by
  induction total with
  | wildcard => intro environment valid value valueValid; exact ⟨[], rfl, .nil⟩
  | bind => intro environment valid value valueValid; exact ⟨_, rfl, .cons valueValid .nil⟩
  | pair left right leftIH rightIH =>
      intro environment valid value valueValid
      cases value with
      | pair first last =>
          exact andThen_matches _ _ (leftIH environment valid first valueValid.1)
            (fun prior priorValid => rightIH (prior ++ environment) (priorValid.append valid) last valueValid.2)
      | literal | record | variant | nominal | list => cases valueValid
  | recordEnd =>
      intro environment valid value valueValid
      cases value with
      | record fields => exact ⟨[], rfl, .nil⟩
      | literal | pair | variant | nominal | list => cases valueValid
  | field admissible child rest childIH restIH =>
      intro environment valid value valueValid
      have fieldValid := admissible value valueValid
      cases value with
      | record fields =>
          obtain ⟨item, found, itemValid⟩ := fieldValid
          simp only [run, found]
          exact andThen_matches _ _ (childIH environment valid item itemValid)
            (fun prior priorValid => restIH (prior ++ environment) (priorValid.append valid)
              (.record fields) valueValid)
      | literal | pair | variant | nominal | list => cases fieldValid
  | defaultField admissible fallbackTyped child restTyped childIH restIH =>
      intro environment valid value valueValid
      have optionalValid := admissible value valueValid
      cases value with
      | record fields =>
          cases found : lookup _ fields with
          | some item =>
              rw [default_present _ _ _ _ _ _ _ _ _ found]
              exact andThen_matches _ _ (childIH environment valid item (Or.inl (optionalValid item found)))
                (fun prior priorValid => restIH (prior ++ environment) (priorValid.append valid)
                  (.record fields) valueValid)
          | none =>
              obtain ⟨item, evaluated, itemValid⟩ := defaults _ _ _ fallbackTyped environment valid
              rw [default_absent _ _ _ _ _ _ _ _ found, Logged.bind_result, evaluated]
              exact andThen_matches _ _ (childIH environment valid item (Or.inr itemValid))
                (fun prior priorValid => restIH (prior ++ environment) (priorValid.append valid)
                  (.record fields) valueValid)
      | literal | pair | variant | nominal | list => cases optionalValid
  | variant child childIH =>
      intro environment valid value valueValid
      cases value with
      | variant name payload =>
          obtain ⟨rfl, payloadValid⟩ := valueValid
          simpa [run] using childIH environment valid payload payloadValid
      | literal | pair | record | nominal | list => cases valueValid
  | nominal child childIH =>
      intro environment valid value valueValid
      cases value with
      | nominal name ctor payload =>
          obtain ⟨rfl, rfl, payloadValid⟩ := valueValid
          simpa [run] using childIH environment valid payload payloadValid
      | literal | pair | record | variant | list => cases valueValid
  | orLeft left right leftIH =>
      intro environment valid value valueValid
      obtain ⟨matched, evaluated, matchedValid⟩ := leftIH environment valid value valueValid
      exact ⟨matched, by simp [run, Logged.bind_result, evaluated, success, Logged.ofResult], matchedValid⟩
  | orRight left right rightIH =>
      intro environment valid value valueValid
      have safe := typing_matches floatCheck defaultEval defaults left environment valid value valueValid
      simp only [run, Logged.bind_result]
      cases observed : (run floatCheck defaultEval environment _ value).result with
      | error error => rw [observed] at safe; cases safe
      | ok option =>
          rw [observed] at safe
          cases option with
          | none => exact rightIH environment valid value valueValid
          | some matched => exact ⟨matched, rfl, safe⟩
  | as child childIH =>
      intro environment valid value valueValid
      obtain ⟨matched, evaluated, matchedValid⟩ := childIH environment valid value valueValid
      exact ⟨_, by simp [run, Logged.bind_result, evaluated, success, Logged.ofResult],
        BindingsHold.cons valueValid matchedValid⟩
  | narrow below child childIH =>
      intro environment valid value valueValid
      exact childIH environment valid value (below value valueValid)

end Yulang.ScopedCasePatterns
