import Yulang.PresenceLayers

/-!
# Exact finite decisions for Boolean record-presence bounds

Fixed bounds here are Boolean combinations of `any`, `never`, `records`,
unrestricted field presence and field absence. They contain no payload bound,
type variable, recursive reference, function or effect row.

Only the labels occurring in the two bounds affect their implication. Every
record profile on those labels has a concrete representative with integer
payloads, and every nonrecord has the same observations as one integer value.
The finite implication scan is therefore complete for arbitrary runtime values.
This enumerates the observations of the *fixed bounds*, never solver variable
parameters or a finite approximation to those parameters.
-/

namespace Yulang.PresenceFiniteBounds

open SourceDataRuntime
open PresenceDataTypes (Ty Le)

inductive Bound where
  | bottom
  | top
  | records
  | present : Nat → Bound
  | absent : Nat → Bound
  | union : Bound → Bound → Bound
  | inter : Bound → Bound → Bound
  deriving Repr, DecidableEq

def denote : Bound → Ty
  | .bottom => PresenceDataTypes.never
  | .top => PresenceDataTypes.any
  | .records => PresenceDataTypes.records
  | .present label => PresenceDataTypes.required label PresenceDataTypes.any
  | .absent label => PresenceDataTypes.lacks label
  | .union left right => PresenceDataTypes.union (denote left) (denote right)
  | .inter left right => PresenceDataTypes.inter (denote left) (denote right)

/-- The declared bound fragment is an actual fragment of existing presence
layers; its one payload reference is interpreted by unrestricted `any`. -/
def toLayer : Bound → PresenceLayers.Layer Unit
  | .bottom => .bottom
  | .top => .top
  | .records => .records
  | .present label => .required label ()
  | .absent label => .lacks label
  | .union left right => .union (toLayer left) (toLayer right)
  | .inter left right => .inter (toLayer left) (toLayer right)

theorem toLayer_exact (bound : Bound) (value : Value) :
    (toLayer bound).denote (fun _ => PresenceDataTypes.any) value ↔ denote bound value := by
  induction bound with
  | union left right ihl ihr => exact or_congr ihl ihr
  | inter left right ihl ihr => exact and_congr ihl ihr
  | present label | absent label => simp [toLayer, PresenceLayers.Layer.denote,
      PresenceLayers.Layer.meaning, denote]
  | _ => rfl

def recordFlag : Value → Bool
  | .record _ => true
  | _ => false

def hasField (value : Value) (label : Nat) : Bool :=
  (PresenceDataTypes.lookup label value).isSome

def check : Bound → Value → Bool
  | .bottom, _ => false
  | .top, _ => true
  | .records, value => recordFlag value
  | .present label, value => hasField value label
  | .absent label, value => recordFlag value && !(hasField value label)
  | .union left right, value => check left value || check right value
  | .inter left right, value => check left value && check right value

theorem check_exact (bound : Bound) (value : Value) :
    check bound value = true ↔ denote bound value := by
  induction bound with
  | bottom | top => simp [check, denote, PresenceDataTypes.never, PresenceDataTypes.any]
  | records => cases value <;> simp [check, recordFlag, denote, PresenceDataTypes.records]
  | present label =>
      cases value with
      | record fields =>
          cases found : Fields.lookup label fields <;>
            simp [check, hasField, denote, PresenceDataTypes.lookup, PresenceDataTypes.required,
              PresenceDataTypes.records, PresenceDataTypes.any, found]
      | _ => simp [check, hasField, denote, PresenceDataTypes.lookup,
          PresenceDataTypes.required, PresenceDataTypes.records]
  | absent label =>
      cases value with
      | record fields =>
          cases found : Fields.lookup label fields <;>
            simp [check, recordFlag, hasField, denote, PresenceDataTypes.lookup,
              PresenceDataTypes.lacks, PresenceDataTypes.records, found]
      | _ => simp [check, recordFlag, hasField, denote, PresenceDataTypes.lookup,
          PresenceDataTypes.lacks, PresenceDataTypes.records]
  | union left right ihl ihr =>
      simpa only [check, Bool.or_eq_true, denote, PresenceDataTypes.union] using or_congr ihl ihr
  | inter left right ihl ihr =>
      simpa only [check, Bool.and_eq_true, denote, PresenceDataTypes.inter] using and_congr ihl ihr

def labels : Bound → List Nat
  | .present label | .absent label => [label]
  | .union left right | .inter left right => labels left ++ labels right
  | _ => []

theorem check_congr (bound : Bound) (first last : Value)
    (sameRecord : recordFlag first = recordFlag last)
    (sameFields : ∀ label ∈ labels bound, hasField first label = hasField last label) :
    check bound first = check bound last := by
  induction bound with
  | bottom | top => rfl
  | records => exact sameRecord
  | present label => exact sameFields label (List.mem_singleton_self label)
  | absent label => simp only [check, sameRecord, sameFields label (List.mem_singleton_self label)]
  | union left right ihl ihr | inter left right ihl ihr =>
      have left := ihl (fun label member => sameFields label (List.mem_append_left _ member))
      have right := ihr (fun label member => sameFields label (List.mem_append_right _ member))
      simp only [check, left, right]

def profiles : List Nat → List (List Nat)
  | [] => [[]]
  | label :: rest => profiles rest ++ (profiles rest).map (label :: ·)

theorem filter_mem_profiles (observed : List Nat) (present : Nat → Bool) :
    observed.filter present ∈ profiles observed := by
  induction observed with
  | nil => simp [profiles]
  | cons label rest ih =>
      cases kept : present label <;> simp [profiles, kept, ih]

def recordOf (present : List Nat) : Value :=
  .record (present.map fun label => (label, .base .int))

theorem recordOf_hasField (present : List Nat) (label : Nat) :
    hasField (recordOf present) label = true ↔ label ∈ present := by
  induction present with
  | nil => simp [recordOf, hasField, PresenceDataTypes.lookup, Fields.lookup]
  | cons name rest ih =>
      by_cases equal : label = name
      · subst name
        simp [recordOf, hasField, PresenceDataTypes.lookup, Fields.lookup]
      · simpa only [recordOf, List.map_cons, hasField, PresenceDataTypes.lookup, Fields.lookup,
          equal, ↓reduceIte, List.mem_cons, false_or] using ih

def representatives (observed : List Nat) : List Value :=
  .base .int :: (profiles observed).map recordOf

def representative (observed : List Nat) (value : Value) : Value :=
  match value with
  | .record _ => recordOf (observed.filter (hasField value))
  | _ => .base .int

theorem representative_mem (observed : List Nat) (value : Value) :
    representative observed value ∈ representatives observed := by
  cases value with
  | record fields =>
      apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨_, filter_mem_profiles observed _, rfl⟩
  | _ => exact List.mem_cons_self

theorem representative_recordFlag (observed : List Nat) (value : Value) :
    recordFlag (representative observed value) = recordFlag value := by
  cases value <;> rfl

theorem representative_hasField (observed : List Nat) (value : Value) (label : Nat)
    (member : label ∈ observed) :
    hasField (representative observed value) label = hasField value label := by
  cases value with
  | record fields =>
      have exact : hasField (representative observed (.record fields)) label = true ↔
          hasField (.record fields) label = true := by
        change hasField (recordOf (observed.filter (hasField (.record fields)))) label = true ↔ _
        rw [recordOf_hasField, List.mem_filter]
        simp [member]
      cases first : hasField (representative observed (.record fields)) label <;>
        cases last : hasField (.record fields) label <;> simp_all
  | _ => rfl

/-- The representative keeps every observation occurring in the bound,
without inspecting or limiting any of the original record payloads. -/
theorem check_representative (observed : List Nat) (bound : Bound)
    (covers : ∀ label ∈ labels bound, label ∈ observed) (value : Value) :
    check bound (representative observed value) = check bound value :=
  check_congr bound _ _ (representative_recordFlag observed value)
    (fun label member => representative_hasField observed value label (covers label member))

/-- This scan has no supplied checker, semantic decision oracle or fuel. -/
def checkLe (left right : Bound) : Bool :=
  (representatives (labels left ++ labels right)).all fun value =>
    !(check left value) || check right value

/-- Exact implication for all bounds in the declared grammar and all data
values, including arbitrarily many unmentioned fields and arbitrary payloads. -/
theorem checkLe_exact (left right : Bound) :
    checkLe left right = true ↔ Le (denote left) (denote right) := by
  simp only [checkLe, List.all_eq_true]
  constructor
  · intro checked value valid
    have leftTrue := (check_exact left value).mpr valid
    have first := check_representative (labels left ++ labels right) left
      (fun label member => List.mem_append_left _ member) value
    have last := check_representative (labels left ++ labels right) right
      (fun label member => List.mem_append_right _ member) value
    have accepted := checked (representative (labels left ++ labels right) value)
      (representative_mem _ value)
    simp only [first, leftTrue, Bool.not_true, Bool.false_or, last] at accepted
    exact (check_exact right value).mp accepted
  · intro below value _
    cases valid : check left value with
    | false => simp
    | true =>
        have accepted := (check_exact right value).mpr (below value ((check_exact left value).mp valid))
        simp [accepted]

theorem checkLe_rejects (left right : Bound) :
    checkLe left right = false ↔ ¬ Le (denote left) (denote right) := by
  rw [← checkLe_exact]
  cases checkLe left right <;> simp

end Yulang.PresenceFiniteBounds
