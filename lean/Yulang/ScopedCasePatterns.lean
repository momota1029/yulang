import Yulang.CasePatterns

/-!
# Pattern defaults in the environment of preceding bindings

This is the environment-threading extension of `CasePatterns.run` for
`spec/03b-patterns.md` 3b.3 (Q4 answer B, Q5/Q6 answer A). Each later
component sees bindings produced by the preceding component in front of its
incoming environment. An or alternative starts with the same incoming
environment, so a failed branch cannot leak bindings into its sibling.

The old scope-independent evaluator remains available, with its original
theorems. `run_constant_defaults` identifies it with this evaluator whenever
default code does not inspect the threaded environment. Names are resolved
identities; source duplicate-binder rejection is a separate static check.
-/

namespace Yulang.ScopedCasePatterns

open CaseValues LiteralValues EvaluationTrace
open CasePatterns (Pattern Observation success miss Holds)

/-- Continue only after a match, passing just the bindings it produced. -/
def andThen (first : Observation F E R)
    (last : Bindings F → Observation F E R) : Observation F E R :=
  first.bind fun result => match result with
    | none => miss
    | some left => (last left).bind fun result => match result with
      | none => miss
      | some right => success (left ++ right)

def run (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (environment : Bindings F) :
    Pattern F D → Value F → Observation F E R
  | .wildcard, _ => success []
  | .bind name, value => success [(name, value)]
  | .literal expected, .literal actual =>
      if matchCheck floatCheck expected actual then success [] else miss
  | .literal _, _ => miss
  | .intRange lower upper, .literal actual =>
      if intRangeCheck lower upper actual then success [] else miss
  | .intRange _ _, _ => miss
  | .pair p q, .pair first last => andThen (run floatCheck defaultEval environment p first)
      (fun prior => run floatCheck defaultEval (prior ++ environment) q last)
  | .pair _ _, _ => miss
  | .recordEnd, .record _ => success []
  | .recordEnd, _ => miss
  | .field name p rest, .record fields =>
      match lookup name fields with
      | none => miss
      | some value => andThen (run floatCheck defaultEval environment p value)
          (fun prior => run floatCheck defaultEval (prior ++ environment) rest (.record fields))
  | .field _ _ _, _ => miss
  | .defaultField name fallback p rest, .record fields =>
      let selected := match lookup name fields with
        | some value => Logged.ofResult (.ok value)
        | none => defaultEval environment fallback
      selected.bind fun value => andThen (run floatCheck defaultEval environment p value)
        (fun prior => run floatCheck defaultEval (prior ++ environment) rest (.record fields))
  | .defaultField _ _ _ _, _ => miss
  | .nil, .list [] => success []
  | .nil, _ => miss
  | .cons p q, .list (first :: rest) => andThen (run floatCheck defaultEval environment p first)
      (fun prior => run floatCheck defaultEval (prior ++ environment) q (.list rest))
  | .cons _ _, _ => miss
  | .snoc p q, .list values =>
      match values.reverse with
      | [] => miss
      | last :: reversed => andThen (run floatCheck defaultEval environment p (.list reversed.reverse))
          (fun prior => run floatCheck defaultEval (prior ++ environment) q last)
  | .snoc _ _, _ => miss
  | .variant tag p, .variant name value =>
      if tag = name then run floatCheck defaultEval environment p value else miss
  | .variant _ _, _ => miss
  | .nominal typeId ctorId p, .nominal actualType actualCtor value =>
      if typeId = actualType ∧ ctorId = actualCtor then run floatCheck defaultEval environment p value else miss
  | .nominal _ _ _, _ => miss
  | .or p q, value => (run floatCheck defaultEval environment p value).bind fun result =>
      match result with
      | some values => success values
      | none => run floatCheck defaultEval environment q value
  | .as p name, value => (run floatCheck defaultEval environment p value).bind fun result =>
      match result with
      | none => miss
      | some values => success ((name, value) :: values)

theorem andThen_constant (first : Observation F E R) (last : Unit → Observation F E R) :
    andThen first (fun _ => last ()) = CasePatterns.andThen first last := rfl

/-- The previous evaluator is exactly the environment-independent special
case, including traces on misses and errors. -/
theorem run_constant_defaults (floatCheck : F → F → Bool)
    (defaultEval : D → Logged E R (Value F)) (environment : Bindings F)
    (pattern : Pattern F D) (value : Value F) :
    run floatCheck (fun _ => defaultEval) environment pattern value =
      CasePatterns.run floatCheck defaultEval pattern value := by
  induction pattern generalizing environment value <;> cases value <;>
    (try simp_all [run, CasePatterns.run, andThen, CasePatterns.andThen]) <;> try rfl
  all_goals
    rename_i values
    cases values <;> simp_all [run, CasePatterns.run, andThen, CasePatterns.andThen] <;> rfl

theorem default_present (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (environment : Bindings F)
    (name : Nat) (fallback : D) (p rest : Pattern F D) (fields : Bindings F) (value : Value F)
    (present : lookup name fields = some value) :
    run floatCheck defaultEval environment (.defaultField name fallback p rest) (.record fields) =
      andThen (run floatCheck defaultEval environment p value)
        (fun prior => run floatCheck defaultEval (prior ++ environment) rest (.record fields)) := by
  simp [run, present, Logged.ofResult, Logged.bind]

theorem default_absent (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (environment : Bindings F)
    (name : Nat) (fallback : D) (p rest : Pattern F D) (fields : Bindings F)
    (absent : lookup name fields = none) :
    run floatCheck defaultEval environment (.defaultField name fallback p rest) (.record fields) =
      (defaultEval environment fallback).bind (fun value =>
        andThen (run floatCheck defaultEval environment p value)
          (fun prior => run floatCheck defaultEval (prior ++ environment) rest (.record fields))) := by
  simp [run, absent]

/-- Misses retain their observations but never invoke the later component. -/
theorem andThen_miss (events : List E) (last : Bindings F → Observation F E R) :
    andThen ⟨events, .ok none⟩ last = ⟨events, .ok none⟩ := by
  simp [andThen, Logged.bind, miss, Logged.ofResult]

/-- A failed or branch contributes its observations, but not its bindings. -/
theorem or_left_miss (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (environment : Bindings F)
    (p q : Pattern F D) (value : Value F) (events : List E)
    (leftMiss : run floatCheck defaultEval environment p value = ⟨events, .ok none⟩) :
    run floatCheck defaultEval environment (.or p q) value =
      (run floatCheck defaultEval environment q value).prepend events := by
  simp [run, leftMiss, Logged.bind, Logged.prepend]

theorem or_left_success (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (environment : Bindings F)
    (p q : Pattern F D) (value : Value F) (events : List E) (bindings : Bindings F)
    (leftMatch : run floatCheck defaultEval environment p value = ⟨events, .ok (some bindings)⟩) :
    run floatCheck defaultEval environment (.or p q) value = ⟨events, .ok (some bindings)⟩ := by
  simp [run, leftMatch, Logged.bind, success, Logged.ofResult]

theorem andThen_holds (first : Observation F E R) (last : Bindings F → Observation F E R)
    (a : Holds left first.result)
    (b : ∀ values, BindingsHold left values → Holds right (last values).result) :
    Holds (left ++ right) (andThen first last).result := by
  cases first with
  | mk trace result =>
      cases result with
      | error error => cases a
      | ok option =>
          cases option with
          | none => trivial
          | some values =>
              have safe := b values a
              cases actual : last values with
              | mk events result =>
                  rw [actual] at safe
                  cases result with
                  | error error => cases safe
                  | ok option =>
                      cases option with
                      | none => simp [andThen, Logged.bind, actual, Holds, miss, Logged.ofResult]
                      | some more =>
                          simpa [andThen, Logged.bind, actual, success, Logged.ofResult, Holds]
                            using BindingsHold.append a safe

/-- Independent typing threads the same lexical environment as execution.
Only a missing-field default is executable code in this judgement. -/
inductive Typing (DefaultTyped : List (Nat × Ty F) → D → Ty F → Prop) :
    List (Nat × Ty F) → Pattern F D → Ty F → List (Nat × Ty F) → Prop where
  | wildcard : Typing DefaultTyped types .wildcard input []
  | bind : Typing DefaultTyped types (.bind name) input [(name, input)]
  | literal : Ty.Le input (Ty.literal expected.kind) →
      Typing DefaultTyped types (.literal expected) input []
  | intRange : Ty.Le input (Ty.literal .int) → lower.isSome ∨ upper.isSome →
      Typing DefaultTyped types (.intRange lower upper) input []
  | pair : Typing DefaultTyped types p a left → Typing DefaultTyped (left ++ types) q b right →
      Typing DefaultTyped types (.pair p q) (Ty.pair a b) (left ++ right)
  | recordEnd : Typing DefaultTyped types .recordEnd Ty.records []
  | field : Ty.Le input (Ty.required name payload) → Typing DefaultTyped types p payload left →
      Typing DefaultTyped (left ++ types) rest input right →
      Typing DefaultTyped types (.field name p rest) input (left ++ right)
  | defaultField : Ty.Le input (Ty.optional name payload) → DefaultTyped types fallback fallbackType →
      Typing DefaultTyped types p (Ty.union payload fallbackType) left →
      Typing DefaultTyped (left ++ types) rest input right →
      Typing DefaultTyped types (.defaultField name fallback p rest) input (left ++ right)
  | nil : Typing DefaultTyped types .nil (Ty.list element) []
  | cons : Typing DefaultTyped types p element left →
      Typing DefaultTyped (left ++ types) rest (Ty.list element) right →
      Typing DefaultTyped types (.cons p rest) (Ty.list element) (left ++ right)
  | snoc : Typing DefaultTyped types init (Ty.list element) left →
      Typing DefaultTyped (left ++ types) p element right →
      Typing DefaultTyped types (.snoc init p) (Ty.list element) (left ++ right)
  | variant : Typing DefaultTyped types p payload bindings →
      Typing DefaultTyped types (.variant tag p) (Ty.variant tag payload) bindings
  | mergedVariant (row : Variants.Merged.Row Nat (Ty F)) :
      Variants.Merged.lookup tag row = some payload → Typing DefaultTyped types p payload bindings →
      Typing DefaultTyped types (.variant tag p) (Ty.variants row) bindings
  | nominal : Typing DefaultTyped types p payload bindings →
      Typing DefaultTyped types (.nominal typeId ctorId p) (Ty.nominal typeId ctorId payload) bindings
  | mergedNominal (row : Variants.Merged.Row Nat (Ty F)) :
      Variants.Merged.lookup ctorId row = some payload → Typing DefaultTyped types p payload bindings →
      Typing DefaultTyped types (.nominal typeId ctorId p) (Ty.nominals typeId row) bindings
  | or : Typing DefaultTyped types p input bindings → Typing DefaultTyped types q input bindings →
      Typing DefaultTyped types (.or p q) input bindings
  | as : Typing DefaultTyped types p input bindings →
      Typing DefaultTyped types (.as p name) input ((name, input) :: bindings)
  | narrow : Ty.Le input original → Typing DefaultTyped types p original bindings →
      Typing DefaultTyped types p input bindings

end Yulang.ScopedCasePatterns
