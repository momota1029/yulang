import Yulang.PresenceDataTypes

/-!
# Finite exact type descriptors for presence-aware data inference

`Shape` is a type-level descriptor, with its own finite field lists and
lookup/insertion operations. Inference computes these descriptors by structural
recursion on the source expression. It never calls the source evaluator.

`Shape.value` interprets a descriptor in the existing abstract literal/data
universe. Exact predicates retain field absence as well as present payloads.
This is a deliberately precise data model; it is not a replacement for the
legacy width-only record types or for regular function types.
-/

namespace Yulang.PresenceDataShapes

open Inference SourceDataRuntime

mutual
  inductive Shape where
    | base : Base → Shape
    | pair : Shape → Shape → Shape
    | record : ShapeFields → Shape
    | variant : Nat → Shape → Shape
    deriving Repr

  inductive ShapeFields where
    | nil : ShapeFields
    | cons : Nat → Shape → ShapeFields → ShapeFields
    deriving Repr
end

mutual
  def Shape.value : Shape → Value
    | .base name => .base name
    | .pair left right => .pair left.value right.value
    | .record fields => .record fields.values
    | .variant label payload => .variant label payload.value

  def ShapeFields.values : ShapeFields → List (Nat × Value)
    | .nil => []
    | .cons label shape rest => (label, shape.value) :: rest.values
end

def Shape.denote (shape : Shape) : PresenceDataTypes.Ty := PresenceDataTypes.exact shape.value

theorem Shape.denote_le_iff (shape : Shape) (type : PresenceDataTypes.Ty) :
    PresenceDataTypes.Le shape.denote type ↔ type shape.value :=
  PresenceDataTypes.exact_le_iff shape.value type

namespace ShapeFields

def lookup (label : Nat) : ShapeFields → Option Shape
  | .nil => none
  | .cons name shape rest => if label = name then some shape else lookup label rest

def append : ShapeFields → ShapeFields → ShapeFields
  | .nil, right => right
  | .cons label shape rest, right => .cons label shape (append rest right)

def erase (label : Nat) : ShapeFields → ShapeFields
  | .nil => .nil
  | .cons name shape rest =>
      if label = name then erase label rest else .cons name shape (erase label rest)

def insert (label : Nat) (shape : Shape) (rest : ShapeFields) : ShapeFields :=
  .cons label shape (erase label rest)

def insertDefault (label : Nat) (shape : Shape) (fields : ShapeFields) : ShapeFields :=
  if (lookup label fields).isSome then fields else append fields (.cons label shape .nil)

@[simp] theorem lookup_values (label : Nat) (fields : ShapeFields) :
    Fields.lookup label fields.values = (lookup label fields).map Shape.value := by
  cases fields with
  | nil => rfl
  | cons name shape rest =>
      by_cases same : label = name <;>
        simp [values, lookup, Fields.lookup, same, lookup_values label rest]

@[simp] theorem append_values (left right : ShapeFields) :
    (append left right).values = left.values ++ right.values := by
  cases left with
  | nil => rfl
  | cons label shape rest => simp [append, values, append_values rest right]

@[simp] theorem erase_values (label : Nat) (fields : ShapeFields) :
    (erase label fields).values = Fields.erase label fields.values := by
  cases fields with
  | nil => rfl
  | cons name shape rest =>
      by_cases same : label = name
      · subst name
        simpa [erase, values, Fields.erase] using erase_values label rest
      · simp [erase, values, Fields.erase, same, erase_values label rest]

@[simp] theorem insert_values (label : Nat) (shape : Shape) (fields : ShapeFields) :
    (insert label shape fields).values = Fields.insert label shape.value fields.values := by
  simp [insert, values, Fields.insert]

@[simp] theorem insertDefault_values (label : Nat) (shape : Shape) (fields : ShapeFields) :
    (insertDefault label shape fields).values =
      Fields.insertDefault label shape.value fields.values := by
  cases found : lookup label fields <;>
    simp [insertDefault, Fields.insertDefault, found, values]

theorem required_of_lookup (label : Nat) (fields : ShapeFields) (shape : Shape)
    (found : lookup label fields = some shape) :
    PresenceDataTypes.Le (Shape.denote (.record fields))
      (PresenceDataTypes.required label shape.denote) := by
  rintro value rfl
  exact ⟨trivial, shape.value, by simp [PresenceDataTypes.lookup, found, Shape.value], rfl⟩

theorem absent_of_lookup (label : Nat) (fields : ShapeFields)
    (missing : lookup label fields = none) :
    PresenceDataTypes.Le (Shape.denote (.record fields)) (PresenceDataTypes.lacks label) := by
  rintro value rfl
  exact ⟨trivial, by simp [PresenceDataTypes.lookup, missing, Shape.value]⟩

end ShapeFields

end Yulang.PresenceDataShapes
