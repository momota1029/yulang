import Yulang.LiteralValues
import Yulang.PresenceDataTypes
import Yulang.VariantsMerged

/-!
# Concrete first-order values for pattern elimination

The existing data evaluator deliberately stores base markers. This value
universe retains literal contents and adds finite lists and resolved nominal
identities without changing that evaluator or any of its theorems. Floating
point interpretation remains an explicit parameter.
-/

namespace Yulang.CaseValues

open LiteralValues

inductive Value (FloatValue : Type := Empty) where
  | literal : Literal FloatValue → Value FloatValue
  | pair : Value FloatValue → Value FloatValue → Value FloatValue
  | record : List (Nat × Value FloatValue) → Value FloatValue
  | variant : Nat → Value FloatValue → Value FloatValue
  | nominal : Nat → Nat → Value FloatValue → Value FloatValue
  | list : List (Value FloatValue) → Value FloatValue
  deriving Repr

abbrev Bindings (FloatValue : Type := Empty) := List (Nat × Value FloatValue)
abbrev Ty (FloatValue : Type := Empty) := Value FloatValue → Prop

def lookup (name : Nat) : Bindings F → Option (Value F)
  | [] => none
  | (key, value) :: rest => if name = key then some value else lookup name rest

namespace Ty

def Le (a b : Ty F) : Prop := ∀ value, a value → b value
def any : Ty F := fun _ => True
def never : Ty F := fun _ => False
def union (a b : Ty F) : Ty F := fun value => a value ∨ b value
def inter (a b : Ty F) : Ty F := fun value => a value ∧ b value
def exact (expected : Value F) : Ty F := fun value => value = expected
def literal (kind : Kind) : Ty F
  | .literal value => value.kind = kind
  | _ => False
def pair (a b : Ty F) : Ty F
  | .pair first last => a first ∧ b last
  | _ => False
def records : Ty F
  | .record _ => True
  | _ => False
def required (name : Nat) (payload : Ty F) : Ty F
  | .record fields => ∃ value, lookup name fields = some value ∧ payload value
  | _ => False
def optional (name : Nat) (payload : Ty F) : Ty F
  | .record fields => ∀ value, lookup name fields = some value → payload value
  | _ => False
def list (element : Ty F) : Ty F
  | .list values => ∀ value ∈ values, element value
  | _ => False
def variant (tag : Nat) (payload : Ty F) : Ty F
  | .variant name value => name = tag ∧ payload value
  | _ => False
def variants (row : Variants.Merged.Row Nat (Ty F)) : Ty F
  | .variant tag value => ∃ payload, Variants.Merged.lookup tag row = some payload ∧ payload value
  | _ => False
def nominal (typeId ctorId : Nat) (payload : Ty F) : Ty F
  | .nominal typeName ctorName value => typeName = typeId ∧ ctorName = ctorId ∧ payload value
  | _ => False
def nominals (typeId : Nat) (row : Variants.Merged.Row Nat (Ty F)) : Ty F
  | .nominal typeName ctorName value => typeName = typeId ∧
      ∃ payload, Variants.Merged.lookup ctorName row = some payload ∧ payload value
  | _ => False

theorem optional_records (name : Nat) (payload : Ty F) : Le (optional name payload) records := by
  intro value valid
  cases value <;> trivial

end Ty

/-- Bindings are checked position by position; no lookup policy is used by
this relation. Name alignment is a separate static obligation. -/
inductive BindingsHold : List (Nat × Ty F) → Bindings F → Prop where
  | nil : BindingsHold [] []
  | cons : type value → BindingsHold types values →
      BindingsHold ((name, type) :: types) ((name, value) :: values)

theorem BindingsHold.append (left : BindingsHold a x) (right : BindingsHold b y) :
    BindingsHold (a ++ b) (x ++ y) := by
  induction left with
  | nil => exact right
  | cons valid _ ih => exact .cons valid ih

theorem BindingsHold.names (valid : BindingsHold types values) :
    values.map Prod.fst = types.map Prod.fst := by
  induction valid with
  | nil => rfl
  | cons _ _ ih => simp [ih]

end Yulang.CaseValues
