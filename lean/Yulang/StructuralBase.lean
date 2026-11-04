import Yulang.Types

/-!
# Structural types over an explicit row algebra

This is the shared reference ground type algebra for the nonnegative and signed
occurrence models. Only arrow variance consults the supplied row relation. The
structural rules, first-field-wins record lookup, and scalar separation are the
same for both interpretations. This is not a subtyping solver, a canonical MLsub
semantics, or a model of recursive source types.
-/

namespace Yulang.StructuralBase

open Yulang.Inference

inductive Ty (RowType : Type u) where
  | base : Base → Ty RowType
  | bottom : Ty RowType
  | union : Ty RowType → Ty RowType → Ty RowType
  | inter : Ty RowType → Ty RowType → Ty RowType
  | pair : Ty RowType → Ty RowType → Ty RowType
  | emptyRecord : Ty RowType
  | record : Nat → Ty RowType → Ty RowType → Ty RowType
  | variant : Nat → Ty RowType → Ty RowType
  | arrow : Ty RowType → RowType → Ty RowType → RowType → Ty RowType

/-- Lookup stops at the first field; a hidden duplicate is not a requirement. -/
def Ty.lookup (label : Nat) : Ty RowType → Option (Ty RowType)
  | .record current value rest => if label = current then some value else rest.lookup label
  | _ => none

inductive IsRecord : Ty RowType → Prop where
  | empty : IsRecord .emptyRecord
  | field : IsRecord rest → IsRecord (.record label value rest)

/-- A structural preorder; it is intentionally not defined by solver success. -/
inductive Subtype (leRow : RowType → RowType → Prop) : Ty RowType → Ty RowType → Prop where
  | refl (a : Ty RowType) : Subtype leRow a a
  | trans : Subtype leRow a b → Subtype leRow b c → Subtype leRow a c
  | bottom (a : Ty RowType) : Subtype leRow .bottom a
  | unionLeft (a b : Ty RowType) : Subtype leRow a (.union a b)
  | unionRight (a b : Ty RowType) : Subtype leRow b (.union a b)
  | unionElim : Subtype leRow a c → Subtype leRow b c → Subtype leRow (.union a b) c
  | interLeft (a b : Ty RowType) : Subtype leRow (.inter a b) a
  | interRight (a b : Ty RowType) : Subtype leRow (.inter a b) b
  | interIntro : Subtype leRow c a → Subtype leRow c b → Subtype leRow c (.inter a b)
  | pair : Subtype leRow a a' → Subtype leRow b b' → Subtype leRow (.pair a b) (.pair a' b')
  | variant : Subtype leRow a b → Subtype leRow (.variant label a) (.variant label b)
  | arrow : Subtype leRow input' input → leRow inputRow' inputRow →
      Subtype leRow output output' → leRow outputRow outputRow' →
      Subtype leRow (.arrow input inputRow output outputRow)
        (.arrow input' inputRow' output' outputRow')
  | record : IsRecord source → IsRecord target →
      (∀ label value, target.lookup label = some value →
        ∃ actual, source.lookup label = some actual) →
      (∀ label actual expected, source.lookup label = some actual →
        target.lookup label = some expected → Subtype leRow actual expected) →
      Subtype leRow source target

/-- The shared type algebra uses the supplied row carrier and operations. -/
def model (RowType : Type u) (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) : Model where
  Ty := Ty RowType
  Row := RowType
  base := Ty.base
  bottom := Ty.bottom
  union := Ty.union
  inter := Ty.inter
  pair := Ty.pair
  emptyRecord := Ty.emptyRecord
  record := Ty.record
  variant := Ty.variant
  arrow := Ty.arrow
  empty := empty
  join := join
  subTy := Subtype leRow
  subRow := leRow

variable {RowType : Type u} {leRow : RowType → RowType → Prop}

theorem union_is_join (a b c : Ty RowType) :
    Subtype leRow (.union a b) c ↔ Subtype leRow a c ∧ Subtype leRow b c := by
  constructor
  · intro h
    exact ⟨.trans (.unionLeft a b) h, .trans (.unionRight a b) h⟩
  · rintro ⟨ha, hb⟩
    exact .unionElim ha hb

theorem inter_is_meet (a b c : Ty RowType) :
    Subtype leRow c (.inter a b) ↔ Subtype leRow c a ∧ Subtype leRow c b := by
  constructor
  · intro h
    exact ⟨.trans h (.interLeft a b), .trans h (.interRight a b)⟩
  · rintro ⟨ha, hb⟩
    exact .interIntro ha hb

theorem union_mono {a a' b b' : Ty RowType} (ha : Subtype leRow a a') (hb : Subtype leRow b b') :
    Subtype leRow (.union a b) (.union a' b') :=
  .unionElim (.trans ha (.unionLeft a' b')) (.trans hb (.unionRight a' b'))

theorem inter_mono {a a' b b' : Ty RowType} (ha : Subtype leRow a a') (hb : Subtype leRow b b') :
    Subtype leRow (.inter a b) (.inter a' b') :=
  .interIntro (.trans (.interLeft a b) ha) (.trans (.interRight a b) hb)

/-! ## Non-vacuity

A scalar observation is a small sound interpretation of this judgement. It
distinguishes base types and unions, without asserting that it characterizes
all structural subtypes or function denotations.
-/

def Scalar (observed : Base) : Ty RowType → Prop
  | .base actual => actual = observed
  | .union a b => Scalar observed a ∨ Scalar observed b
  | .inter a b => Scalar observed a ∧ Scalar observed b
  | _ => False

theorem record_not_scalar (observed : Base) {record : Ty RowType} (shape : IsRecord record) :
    ¬ Scalar observed record := by
  cases shape <;> simp [Scalar]

theorem scalar_preserved {a b : Ty RowType} (subtype : Subtype leRow a b) :
    ∀ observed, Scalar observed a → Scalar observed b := by
  induction subtype with
  | refl => exact fun _ h => h
  | trans _ _ ihab ihbc => exact fun observed h => ihbc observed (ihab observed h)
  | bottom => exact fun _ h => False.elim h
  | unionLeft => exact fun _ h => Or.inl h
  | unionRight => exact fun _ h => Or.inr h
  | unionElim _ _ iha ihb => exact fun observed h => h.elim (iha observed) (ihb observed)
  | interLeft => exact fun _ h => h.1
  | interRight => exact fun _ h => h.2
  | interIntro _ _ iha ihb => exact fun observed h => ⟨iha observed h, ihb observed h⟩
  | pair => exact fun _ h => False.elim h
  | variant => exact fun _ h => False.elim h
  | arrow => exact fun _ h => False.elim h
  | record sourceShape _ _ _ _ =>
    exact fun observed h => False.elim (record_not_scalar observed sourceShape h)

theorem distinct_bases_not_subtypes {left right : Base} (different : left ≠ right) :
    ¬ Subtype leRow (Ty.base left : Ty RowType) (.base right) := by
  intro h
  exact different ((scalar_preserved h left rfl).symm)

theorem int_not_str : ¬ Subtype leRow (Ty.base .int : Ty RowType) (.base .str) :=
  distinct_bases_not_subtypes (by decide)

theorem str_not_int : ¬ Subtype leRow (Ty.base .str : Ty RowType) (.base .int) :=
  distinct_bases_not_subtypes (by decide)

theorem int_union_str_not_int :
    ¬ Subtype leRow (Ty.union (.base .int) (.base .str) : Ty RowType) (.base .int) := by
  intro h
  exact str_not_int (.trans (.unionRight _ _) h)

/-! ## Record and variance witnesses -/

@[simp] theorem lookup_first (label : Nat) (head tail : Ty RowType) :
    (Ty.record label head tail).lookup label = some head := by
  simp [Ty.lookup]

@[simp] theorem lookup_other (label other : Nat) (different : label ≠ other)
    (head tail : Ty RowType) :
    (Ty.record other head tail).lookup label = tail.lookup label := by
  simp [Ty.lookup, different]

theorem first_field_wins (label : Nat) (first hidden tail : Ty RowType) :
    (Ty.record label first (.record label hidden tail)).lookup label = some first := by
  simp

theorem record_width :
    Subtype leRow (Ty.record 0 (.base .int) (.record 1 (.base .str) .emptyRecord) : Ty RowType)
      (.record 0 (.base .int) .emptyRecord) := by
  apply Subtype.record (.field (.field .empty)) (.field .empty)
  · intro label value h
    by_cases hl : label = 0
    · subst label
      exact ⟨.base .int, by simp⟩
    · simp [Ty.lookup, hl] at h
  · intro label actual expected ha he
    by_cases hl : label = 0
    · subst label
      simp at ha he
      cases ha
      cases he
      exact .refl _
    · simp [Ty.lookup, hl] at he

theorem record_width_to_empty {record : Ty RowType} (shape : IsRecord record) :
    Subtype leRow record .emptyRecord := by
  apply Subtype.record shape .empty
  · intro label value h
    cases h
  · intro label actual expected _ h
    cases h

/-- Dropping a shadowing int head would expose str and fails the field obligation. -/
theorem shadowed_field_obligation_rejected :
    ¬ (∀ label actual expected,
      (Ty.record 0 (.base .int) (.record 0 (.base .str) .emptyRecord) : Ty RowType).lookup
        label = some actual →
      (Ty.record 0 (.base .str) .emptyRecord : Ty RowType).lookup label = some expected →
      Subtype leRow actual expected) := by
  intro obligation
  exact int_not_str (obligation 0 (.base .int) (.base .str) (by simp) (by simp))

end Yulang.StructuralBase
