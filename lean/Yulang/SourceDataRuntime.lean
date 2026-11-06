import Yulang.Inference

/-!
# An untyped evaluator for the original data core

The input is `Inference.Expr`, not an intrinsically typed or shape-resolved AST.
Values contain actual finite records. Extending a record removes every older
field with the same label, so a hidden payload is not retained in the result.
Both the new head and the old tail are evaluated before this removal.
Spread-first default extension evaluates its base before its fallback, even
when an existing field wins. An absent field is appended after the base fields.

This pure fragment includes variables, literals, pairs and projections,
records and field selection, variants, and evaluated nonrecursive lets.
Literal payloads are abstracted to their base tags, just as in the existing
core AST. Functions, application, conditionals and effects are outside this
evaluator; they return `unsupported`, not a fabricated runtime result.
No input type, shape certificate, inferred plan or fuel is required.
-/

namespace Yulang.SourceDataRuntime

open Inference

inductive Value where
  | base : Base → Value
  | pair : Value → Value → Value
  | record : List (Nat × Value) → Value
  | variant : Nat → Value → Value
  deriving Repr

namespace Fields

def lookup (label : Nat) : List (Nat × Value) → Option Value
  | [] => none
  | (name, value) :: rest => if label = name then some value else lookup label rest

def erase (label : Nat) : List (Nat × Value) → List (Nat × Value)
  | [] => []
  | (name, value) :: rest =>
      if label = name then erase label rest else (name, value) :: erase label rest

def insert (label : Nat) (value : Value) (rest : List (Nat × Value)) : List (Nat × Value) :=
  (label, value) :: erase label rest

/-- First-field-wins fallback insertion, after both expressions have run. -/
def insertDefault (label : Nat) (value : Value) (fields : List (Nat × Value)) :
    List (Nat × Value) :=
  if (lookup label fields).isSome then fields else fields ++ [(label, value)]

theorem lookup_append (label : Nat) (left right : List (Nat × Value)) :
    lookup label (left ++ right) = (lookup label left).or (lookup label right) := by
  induction left with
  | nil => rfl
  | cons field rest ih =>
      obtain ⟨name, value⟩ := field
      by_cases same : label = name <;> simp [lookup, same, ih]

theorem insertDefault_present (label : Nat) (value existing : Value)
    (fields : List (Nat × Value)) (present : lookup label fields = some existing) :
    insertDefault label value fields = fields := by
  simp [insertDefault, present]

theorem insertDefault_absent (label : Nat) (value : Value)
    (fields : List (Nat × Value)) (absent : lookup label fields = none) :
    insertDefault label value fields = fields ++ [(label, value)] := by
  simp [insertDefault, absent]

@[simp] theorem lookup_insertDefault_same (label : Nat) (value : Value)
    (fields : List (Nat × Value)) :
    lookup label (insertDefault label value fields) =
      (lookup label fields).or (some value) := by
  cases found : lookup label fields <;> simp [insertDefault, found, lookup_append, lookup]

theorem lookup_insertDefault_other (label query : Nat) (value : Value)
    (different : query ≠ label) (fields : List (Nat × Value)) :
    lookup query (insertDefault label value fields) = lookup query fields := by
  cases found : lookup label fields <;>
    simp [insertDefault, found, lookup_append, lookup, different]

@[simp] theorem lookup_erase_same (label : Nat) (fields : List (Nat × Value)) :
    lookup label (erase label fields) = none := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
      obtain ⟨name, value⟩ := field
      by_cases same : label = name
      · subst name; simpa [erase] using ih
      · simp [erase, lookup, same, ih]

theorem lookup_erase_other (label query : Nat) (different : query ≠ label)
    (fields : List (Nat × Value)) :
    lookup query (erase label fields) = lookup query fields := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
      obtain ⟨name, value⟩ := field
      by_cases same : label = name
      · subst name
        simp [erase, lookup, different, ih]
      · simp [erase, lookup, same, ih]

@[simp] theorem lookup_insert_same (label : Nat) (value : Value)
    (fields : List (Nat × Value)) : lookup label (insert label value fields) = some value := by
  simp [insert, lookup]

theorem lookup_insert_other (label query : Nat) (value : Value)
    (different : query ≠ label) (fields : List (Nat × Value)) :
    lookup query (insert label value fields) = lookup query fields := by
  simp [insert, lookup, different, lookup_erase_other label query different]

@[simp] theorem erase_idempotent (label : Nat) (fields : List (Nat × Value)) :
    erase label (erase label fields) = erase label fields := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
      obtain ⟨name, value⟩ := field
      by_cases same : label = name
      · subst name; simpa [erase] using ih
      · simp [erase, same, ih]

/-- Shadowed data are erased from the stored record, not merely skipped by lookup. -/
@[simp] theorem insert_shadow (label : Nat) (first hidden : Value)
    (fields : List (Nat × Value)) :
    insert label first (insert label hidden fields) = insert label first fields := by
  simp [insert, erase]

theorem erased_field_absent (label : Nat) (fields : List (Nat × Value))
    (value : Value) : (label, value) ∉ erase label fields := by
  induction fields with
  | nil => simp [erase]
  | cons field rest ih =>
      obtain ⟨name, item⟩ := field
      by_cases same : label = name
      · subst name; simpa [erase] using ih
      · simp [erase, same, ih]

end Fields

inductive Error where
  | unsupported
  | unboundVariable : Nat → Error
  | expectedPair
  | expectedRecord
  | missingField : Nat → Error
  deriving Repr, DecidableEq

abbrev Result := Except Error Value

def eval (environment : List Value) : Expr → Result
  | .var index =>
      match environment[index]? with
      | some value => .ok value
      | none => .error (.unboundVariable index)
  | .lit base => .ok (.base base)
  | .letE value body => do
      let value ← eval environment value
      eval (value :: environment) body
  | .pair left right => do
      let first ← eval environment left
      let last ← eval environment right
      pure (.pair first last)
  | .fst expression => do
      let value ← eval environment expression
      match value with
      | .pair first _ => pure first
      | _ => .error .expectedPair
  | .snd expression => do
      let value ← eval environment expression
      match value with
      | .pair _ last => pure last
      | _ => .error .expectedPair
  | .emptyRecord => .ok (.record [])
  | .record label head tail => do
      let first ← eval environment head
      let last ← eval environment tail
      match last with
      | .record fields => pure (.record (Fields.insert label first fields))
      | _ => .error .expectedRecord
  | .recordDefault label base fallback => do
      let first ← eval environment base
      let last ← eval environment fallback
      match first with
      | .record fields => pure (.record (Fields.insertDefault label last fields))
      | _ => .error .expectedRecord
  | .field label expression => do
      let value ← eval environment expression
      match value with
      | .record fields =>
          match Fields.lookup label fields with
          | some value => pure value
          | none => .error (.missingField label)
      | _ => .error .expectedRecord
  | .variant label expression => do
      let value ← eval environment expression
      pure (.variant label value)
  | _ => .error .unsupported

/-- This syntax predicate does not require successful evaluation or typing. -/
def Supported : Expr → Prop
  | .var _ | .lit _ | .emptyRecord => True
  | .letE left right | .pair left right | .record _ left right | .recordDefault _ left right =>
      Supported left ∧ Supported right
  | .fst expression | .snd expression | .field _ expression | .variant _ expression =>
      Supported expression
  | _ => False

end Yulang.SourceDataRuntime
