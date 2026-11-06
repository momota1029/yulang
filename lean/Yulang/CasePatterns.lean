import Yulang.CaseValues
import Yulang.EvaluationTrace

/-!
# Ordered patterns with lazy defaults

This is a resolved first-order pattern kernel. Tuple, record and list sugar is
represented by binary decomposition; a record tail is matched against the
whole input, whereas a list tail receives only the remaining elements.
Default code is abstract and is invoked only for a missing field. Its lexical
environment, effects, and source name resolution belong to the caller.
No rule about default-expression scope or effect rollback is chosen here.

Answered Q5 agrees with this kernel: matching proceeds from left to right
and stops the remainder of a compound pattern on a miss, so a later
missing-field default is skipped after an earlier mismatch. Answered Q6
also agrees: take the first matching branch; a later failed arm guard does
not retry the other branch. These are ordinary pattern rules, not an
inference from the parser DSL choice rule.

Q4's accumulated default environment is implemented by ScopedCasePatterns;
this environment-independent evaluator remains its proved special case.
Q7's rejection of repeated binders on one path is implemented separately
by PatternBindingChecks. Raw repeated identities here do not constitute
a source shadowing policy or bypass that check.
-/

namespace Yulang.CasePatterns

open CaseValues LiteralValues EvaluationTrace

inductive Pattern (F Default : Type) where
  | wildcard
  | bind : Nat → Pattern F Default
  | literal : Literal F → Pattern F Default
  | intRange : Option Int → Option Int → Pattern F Default
  | pair : Pattern F Default → Pattern F Default → Pattern F Default
  | recordEnd
  | field : Nat → Pattern F Default → Pattern F Default → Pattern F Default
  | defaultField : Nat → Default → Pattern F Default → Pattern F Default → Pattern F Default
  | nil
  | cons : Pattern F Default → Pattern F Default → Pattern F Default
  | snoc : Pattern F Default → Pattern F Default → Pattern F Default
  | variant : Nat → Pattern F Default → Pattern F Default
  | nominal : Nat → Nat → Pattern F Default → Pattern F Default
  | or : Pattern F Default → Pattern F Default → Pattern F Default
  | as : Pattern F Default → Nat → Pattern F Default
  deriving Repr

def Pattern.names : Pattern F D → List Nat
  | .wildcard | .literal _ | .intRange _ _ | .recordEnd | .nil => []
  | .bind name => [name]
  | .pair p q | .field _ p q | .defaultField _ _ p q | .cons p q | .snoc p q => p.names ++ q.names
  | .variant _ p | .nominal _ _ p | .or p _ => p.names
  | .as p name => name :: p.names

def sameNames (left right : List Nat) : Bool :=
  left.all (fun name => decide (name ∈ right)) && right.all (fun name => decide (name ∈ left))

theorem sameNames_exact (left right : List Nat) :
    sameNames left right = true ↔ ∀ name, name ∈ left ↔ name ∈ right := by
  simp only [sameNames, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro both name
    exact ⟨both.1 name, both.2 name⟩
  · intro both
    exact ⟨fun name member => (both name).mp member, fun name member => (both name).mpr member⟩

/-- Source or-patterns compare name sets, not traversal order. The positional
typing interface below still expects elaboration to align its binder order. -/
def Pattern.aligned : Pattern F D → Bool
  | .pair p q | .field _ p q | .defaultField _ _ p q | .cons p q | .snoc p q => p.aligned && q.aligned
  | .variant _ p | .nominal _ _ p | .as p _ => p.aligned
  | .or p q => p.aligned && q.aligned && sameNames p.names q.names
  | .intRange none none => false
  | _ => true

abbrev Observation (F Event Error : Type) := Logged Event Error (Option (Bindings F))

def success (values : Bindings F) : Observation F E R := Logged.ofResult (.ok (some values))
def miss : Observation F E R := Logged.ofResult (.ok none)

/-- Later components are attempted only if earlier components matched. -/
def andThen (first : Observation F E R) (last : Unit → Observation F E R) : Observation F E R :=
  first.bind fun result => match result with
    | none => miss
    | some left => (last ()).bind fun result => match result with
      | none => miss
      | some right => success (left ++ right)

def run (floatCheck : F → F → Bool) (defaultEval : D → Logged E R (Value F)) :
    Pattern F D → Value F → Observation F E R
  | .wildcard, _ => success []
  | .bind name, value => success [(name, value)]
  | .literal expected, .literal actual =>
      if matchCheck floatCheck expected actual then success [] else miss
  | .literal _, _ => miss
  | .intRange lower upper, .literal actual =>
      if intRangeCheck lower upper actual then success [] else miss
  | .intRange _ _, _ => miss
  | .pair p q, .pair first last => andThen (run floatCheck defaultEval p first)
      (fun _ => run floatCheck defaultEval q last)
  | .pair _ _, _ => miss
  | .recordEnd, .record _ => success []
  | .recordEnd, _ => miss
  | .field name p rest, .record fields =>
      match lookup name fields with
      | none => miss
      | some value => andThen (run floatCheck defaultEval p value)
          (fun _ => run floatCheck defaultEval rest (.record fields))
  | .field _ _ _, _ => miss
  | .defaultField name fallback p rest, .record fields =>
      let selected := match lookup name fields with
        | some value => Logged.ofResult (.ok value)
        | none => defaultEval fallback
      selected.bind fun value => andThen (run floatCheck defaultEval p value)
        (fun _ => run floatCheck defaultEval rest (.record fields))
  | .defaultField _ _ _ _, _ => miss
  | .nil, .list [] => success []
  | .nil, _ => miss
  | .cons p q, .list (first :: rest) => andThen (run floatCheck defaultEval p first)
      (fun _ => run floatCheck defaultEval q (.list rest))
  | .cons _ _, _ => miss
  | .snoc p q, .list values =>
      match values.reverse with
      | [] => miss
      | last :: reversed => andThen (run floatCheck defaultEval p (.list reversed.reverse))
          (fun _ => run floatCheck defaultEval q last)
  | .snoc _ _, _ => miss
  | .variant tag p, .variant name value =>
      if tag = name then run floatCheck defaultEval p value else miss
  | .variant _ _, _ => miss
  | .nominal typeId ctorId p, .nominal actualType actualCtor value =>
      if typeId = actualType ∧ ctorId = actualCtor then run floatCheck defaultEval p value else miss
  | .nominal _ _ _, _ => miss
  | .or p q, value => (run floatCheck defaultEval p value).bind fun result =>
      match result with
      | some values => success values
      | none => run floatCheck defaultEval q value
  | .as p name, value => (run floatCheck defaultEval p value).bind fun result =>
      match result with
      | none => miss
      | some values => success ((name, value) :: values)

/-- Present fields do not execute fallback code, including its observations. -/
theorem default_present (floatCheck : F → F → Bool) (defaultEval : D → Logged E R (Value F))
    (name : Nat) (fallback : D) (p rest : Pattern F D) (fields : Bindings F) (value : Value F)
    (present : lookup name fields = some value) :
    run floatCheck defaultEval (.defaultField name fallback p rest) (.record fields) =
      andThen (run floatCheck defaultEval p value)
        (fun _ => run floatCheck defaultEval rest (.record fields)) := by
  simp [run, present, Logged.ofResult, Logged.bind]

theorem default_absent (floatCheck : F → F → Bool) (defaultEval : D → Logged E R (Value F))
    (name : Nat) (fallback : D) (p rest : Pattern F D) (fields : Bindings F)
    (absent : lookup name fields = none) :
    run floatCheck defaultEval (.defaultField name fallback p rest) (.record fields) =
      (defaultEval fallback).bind (fun value => andThen (run floatCheck defaultEval p value)
        (fun _ => run floatCheck defaultEval rest (.record fields))) := by
  simp [run, absent]

def Holds (types : List (Nat × Ty F)) : Except R (Option (Bindings F)) → Prop
  | .error _ => False
  | .ok none => True
  | .ok (some values) => BindingsHold types values

theorem success_holds (values : Bindings F) (valid : BindingsHold types values) :
    Holds types (success (E := E) (R := R) values).result := valid

theorem andThen_holds (first : Observation F E R) (last : Unit → Observation F E R)
    (a : Holds left first.result) (b : Holds right (last ()).result) :
    Holds (left ++ right) (andThen first last).result := by
  cases first with
  | mk trace result =>
      cases result with
      | error error => cases a
      | ok option =>
          cases option with
          | none => trivial
          | some values =>
              cases actual : last () with
              | mk events result =>
                  rw [actual] at b
                  cases result with
                  | error error => cases b
                  | ok option =>
                      cases option with
                      | none => simp [andThen, Logged.bind, actual, Holds, miss, Logged.ofResult]
                      | some more =>
                          simpa [andThen, Logged.bind, actual, success, Logged.ofResult, Holds]
                            using BindingsHold.append a b

/-- Independent pattern typing. In particular a default receives the union
of the optional field payload and the fallback type, as in decision 44. -/
inductive Typing (DefaultTyped : D → Ty F → Prop) :
    Pattern F D → Ty F → List (Nat × Ty F) → Prop where
  | wildcard : Typing DefaultTyped .wildcard input []
  | bind : Typing DefaultTyped (.bind name) input [(name, input)]
  | literal : Ty.Le input (Ty.literal expected.kind) → Typing DefaultTyped (.literal expected) input []
  | intRange : Ty.Le input (Ty.literal .int) → lower.isSome ∨ upper.isSome →
      Typing DefaultTyped (.intRange lower upper) input []
  | pair : Typing DefaultTyped p a left → Typing DefaultTyped q b right →
      Typing DefaultTyped (.pair p q) (Ty.pair a b) (left ++ right)
  | recordEnd : Typing DefaultTyped .recordEnd Ty.records []
  | field : Ty.Le input (Ty.required name payload) → Typing DefaultTyped p payload left →
      Typing DefaultTyped rest input right → Typing DefaultTyped (.field name p rest) input (left ++ right)
  | defaultField : Ty.Le input (Ty.optional name payload) → DefaultTyped fallback fallbackType →
      Typing DefaultTyped p (Ty.union payload fallbackType) left → Typing DefaultTyped rest input right →
      Typing DefaultTyped (.defaultField name fallback p rest) input (left ++ right)
  | nil : Typing DefaultTyped .nil (Ty.list element) []
  | cons : Typing DefaultTyped p element left → Typing DefaultTyped rest (Ty.list element) right →
      Typing DefaultTyped (.cons p rest) (Ty.list element) (left ++ right)
  | snoc : Typing DefaultTyped init (Ty.list element) left → Typing DefaultTyped p element right →
      Typing DefaultTyped (.snoc init p) (Ty.list element) (left ++ right)
  | variant : Typing DefaultTyped p payload bindings →
      Typing DefaultTyped (.variant tag p) (Ty.variant tag payload) bindings
  | mergedVariant (row : Variants.Merged.Row Nat (Ty F)) :
      Variants.Merged.lookup tag row = some payload → Typing DefaultTyped p payload bindings →
      Typing DefaultTyped (.variant tag p) (Ty.variants row) bindings
  | nominal : Typing DefaultTyped p payload bindings →
      Typing DefaultTyped (.nominal typeId ctorId p) (Ty.nominal typeId ctorId payload) bindings
  | mergedNominal (row : Variants.Merged.Row Nat (Ty F)) :
      Variants.Merged.lookup ctorId row = some payload → Typing DefaultTyped p payload bindings →
      Typing DefaultTyped (.nominal typeId ctorId p) (Ty.nominals typeId row) bindings
  | or : Typing DefaultTyped p input bindings → Typing DefaultTyped q input bindings →
      Typing DefaultTyped (.or p q) input bindings
  | as : Typing DefaultTyped p input bindings →
      Typing DefaultTyped (.as p name) input ((name, input) :: bindings)
  | narrow : Ty.Le input original → Typing DefaultTyped p original bindings →
      Typing DefaultTyped p input bindings

end Yulang.CasePatterns
