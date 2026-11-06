import Yulang.CasePatterns

/-!
# Independent pattern typing implies safe matching

Defaults are the only executable leaves of a pattern. The theorem quantifies
over their implementation and requires its ordinary typing soundness contract.
It does not assume successful matching: literal, range and list alternatives
may miss. A successful match produces precisely the declared typed bindings.
-/

namespace Yulang.CasePatterns

open CaseValues LiteralValues EvaluationTrace

def DefaultSound (DefaultTyped : D → Ty F → Prop) (defaultEval : D → Logged E R (Value F)) : Prop :=
  ∀ code type, DefaultTyped code type →
    ∃ value, (defaultEval code).result = .ok value ∧ type value

theorem Typing.binding_names (typed : Typing DefaultTyped pattern input bindings) :
    pattern.names = bindings.map Prod.fst := by
  induction typed <;> simp_all [Pattern.names]

theorem Typing.aligned (typed : Typing DefaultTyped pattern input bindings) :
    pattern.aligned = true := by
  induction typed with
  | wildcard | bind | literal | recordEnd | nil => rfl
  | @intRange input lower upper _ valid =>
      cases lower <;> cases upper <;> simp_all [Pattern.aligned]
  | pair _ _ left right | field _ _ _ left right | defaultField _ _ _ _ left right
    | cons _ _ left right | snoc _ _ left right => simp [Pattern.aligned, left, right]
  | variant _ child | mergedVariant _ _ _ child | nominal _ child | mergedNominal _ _ _ child
    | as _ child => exact child
  | or left right leftIH rightIH =>
      simp only [Pattern.aligned, leftIH, rightIH, Bool.true_and]
      apply (sameNames_exact _ _).mpr
      intro name
      rw [left.binding_names, right.binding_names]
  | narrow _ _ child => exact child

theorem typing_matches (floatCheck : F → F → Bool)
    (defaultEval : D → Logged E R (Value F))
    (defaults : DefaultSound DefaultTyped defaultEval)
    (typed : Typing DefaultTyped pattern input bindings)
    (value : Value F) (valid : input value) :
    Holds bindings (run floatCheck defaultEval pattern value).result := by
  induction typed generalizing value with
  | wildcard => exact .nil
  | bind => exact .cons valid .nil
  | literal admissible =>
      cases value <;> simp only [run]
      all_goals first
        | (split <;> simp [success, miss, Logged.ofResult, Holds, BindingsHold.nil])
        | (exact True.intro)
  | intRange admissible bound =>
      cases value <;> simp only [run]
      all_goals first
        | (split <;> simp [success, miss, Logged.ofResult, Holds, BindingsHold.nil])
        | (exact True.intro)
  | pair left right leftIH rightIH =>
      cases value with
      | pair first last => exact andThen_holds _ _ (leftIH first valid.1) (rightIH last valid.2)
      | literal | record | variant | nominal | list => cases valid
  | recordEnd =>
      cases value with
      | record fields => exact .nil
      | literal | pair | variant | nominal | list => cases valid
  | field admissible child rest childIH restIH =>
      have fieldValid := admissible value valid
      cases value with
      | record fields =>
          obtain ⟨item, found, itemValid⟩ := fieldValid
          simp only [run, found]
          exact andThen_holds _ _ (childIH item itemValid) (restIH (.record fields) valid)
      | literal | pair | variant | nominal | list => cases fieldValid
  | @defaultField input name payload fallback fallbackType p left rest right admissible fallbackTyped child restTyped childIH restIH =>
      have optionalValid := admissible value valid
      cases value with
      | record fields =>
          cases found : lookup name fields with
          | some item =>
              rw [default_present _ _ _ _ _ _ _ _ found]
              exact andThen_holds _ _ (childIH item (Or.inl (optionalValid item found)))
                (restIH (.record fields) valid)
          | none =>
              obtain ⟨item, evaluated, itemValid⟩ := defaults fallback fallbackType fallbackTyped
              rw [default_absent _ _ _ _ _ _ _ found, Logged.bind_result, evaluated]
              exact andThen_holds _ _ (childIH item (Or.inr itemValid)) (restIH (.record fields) valid)
      | literal | pair | variant | nominal | list => cases optionalValid
  | nil =>
      cases value with
      | list values => cases values <;> first | exact BindingsHold.nil | exact True.intro
      | literal | pair | record | variant | nominal => cases valid
  | cons head rest headIH restIH =>
      cases value with
      | list values =>
          cases values with
          | nil => trivial
          | cons first more =>
              exact andThen_holds _ _ (headIH first (valid first (by simp)))
                (restIH (.list more) (fun item member => valid item (by simp [member])))
      | literal | pair | record | variant | nominal => cases valid
  | snoc init last initIH lastIH =>
      cases value with
      | list values =>
          cases reversed : values.reverse with
          | nil => simp [run, reversed, miss, Logged.ofResult, Holds]
          | cons final earlier =>
              have original : values = earlier.reverse ++ [final] := by
                have same := congrArg List.reverse reversed
                simpa using same
              simp only [run, reversed]
              refine andThen_holds _ _ (initIH (.list earlier.reverse) ?_) (lastIH final ?_)
              · intro item member
                apply valid item
                rw [original]
                simp [member]
              · apply valid final
                rw [original]
                simp
      | literal | pair | record | variant | nominal => cases valid
  | variant child childIH =>
      cases value with
      | variant name payload =>
          obtain ⟨rfl, payloadValid⟩ := valid
          simpa [run] using childIH payload payloadValid
      | literal | pair | record | nominal | list => cases valid
  | @mergedVariant tag payload p bindings row found child childIH =>
      cases value with
      | variant name item =>
          by_cases same : tag = name
          · subst name
            obtain ⟨actual, actualFound, itemValid⟩ := valid
            have equal : actual = payload := Option.some.inj (actualFound.symm.trans found)
            subst actual
            simpa [run] using childIH item itemValid
          · simp [run, same, Holds, miss, Logged.ofResult]
      | literal | pair | record | nominal | list => cases valid
  | nominal child childIH =>
      cases value with
      | nominal name ctor payload =>
          obtain ⟨rfl, rfl, payloadValid⟩ := valid
          simpa [run] using childIH payload payloadValid
      | literal | pair | record | variant | list => cases valid
  | @mergedNominal ctorId payload p bindings typeId row found child childIH =>
      cases value with
      | nominal typeName ctorName item =>
          obtain ⟨rfl, actual, actualFound, itemValid⟩ := valid
          by_cases same : ctorId = ctorName
          · subst ctorName
            have equal : actual = payload := Option.some.inj (actualFound.symm.trans found)
            subst actual
            simpa [run] using childIH item itemValid
          · simp [run, same, Holds, miss, Logged.ofResult]
      | literal | pair | record | variant | list => cases valid
  | or left right leftIH rightIH =>
      have first := leftIH value valid
      simp only [run, Logged.bind_result]
      cases observed : (run floatCheck defaultEval _ value).result with
      | error error => rw [observed] at first; cases first
      | ok option =>
          rw [observed] at first
          cases option with
          | none => exact rightIH value valid
          | some values => exact first
  | as child childIH =>
      have matched := childIH value valid
      simp only [run, Logged.bind_result]
      cases observed : (run floatCheck defaultEval _ value).result with
      | error error => rw [observed] at matched; cases matched
      | ok option =>
          rw [observed] at matched
          cases option with
          | none => trivial
          | some values => exact BindingsHold.cons valid matched
  | narrow below child childIH => exact childIH value (below value valid)

theorem typed_match_no_error (floatCheck : F → F → Bool)
    (defaultEval : D → Logged E R (Value F))
    (defaults : DefaultSound DefaultTyped defaultEval)
    (typed : Typing DefaultTyped pattern input bindings)
    (value : Value F) (valid : input value) (error : R) :
    (run floatCheck defaultEval pattern value).result ≠ .error error := by
  intro failed
  have safe := typing_matches floatCheck defaultEval defaults typed value valid
  rw [failed] at safe
  exact safe

theorem typed_match_bindings (floatCheck : F → F → Bool)
    (defaultEval : D → Logged E R (Value F))
    (defaults : DefaultSound DefaultTyped defaultEval)
    (typed : Typing DefaultTyped pattern input bindings)
    (value : Value F) (valid : input value) (matched : Bindings F)
    (success : (run floatCheck defaultEval pattern value).result = .ok (some matched)) :
    BindingsHold bindings matched := by
  have safe := typing_matches floatCheck defaultEval defaults typed value valid
  simpa [success, Holds] using safe

end Yulang.CasePatterns
