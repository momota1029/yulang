import Yulang.SemanticRecords

/-!
# Record types identified by semantic equivalence

The quotient is taken after closing the structural preorder under record
congruence. Quotienting the old preorder directly would not define a record
operation: equivalent tails could produce inequivalent records.

All type constructors below are well-defined operations on the quotient.
The order is induced by the independently defined `SemanticRecords.Subtype`;
quotient equality is exactly mutual subtyping. This module does not define
an executable canonical display or a subtype decision procedure.
-/

namespace Yulang.SemanticRecordQuotient

open Inference
open StructuralBase (Ty)
open SemanticRecords (Subtype Equivalent)

universe u

variable {Row : Type u}

def typeSetoid (leRow : Row → Row → Prop) : Setoid (Ty Row) where
  r := Equivalent leRow
  iseqv := ⟨Equivalent.refl, Equivalent.symm, Equivalent.trans⟩

abbrev QTy (leRow : Row → Row → Prop) := Quotient (typeSetoid leRow)

variable {leRow : Row → Row → Prop}

def mk (type : Ty Row) : QTy leRow := Quotient.mk (typeSetoid leRow) type

@[simp] theorem mk_eq_mk_iff (a b : Ty Row) :
    mk (leRow := leRow) a = mk b ↔ Equivalent leRow a b := by
  constructor
  · exact Quotient.exact
  · intro same
    exact Quotient.sound (s := typeSetoid leRow) same

/-- Semantic subtyping is independent of the choice of representatives. -/
def le : QTy leRow → QTy leRow → Prop :=
  Quotient.lift₂ (Subtype leRow) (fun _ _ _ _ left right =>
    propext ⟨fun below => .trans left.2 (.trans below right.1),
      fun below => .trans left.1 (.trans below right.2)⟩)

@[simp] theorem le_mk_iff (a b : Ty Row) :
    le (mk (leRow := leRow) a) (mk b) ↔ Subtype leRow a b := Iff.rfl

theorem le_refl (a : QTy leRow) : le a a := by
  refine Quotient.inductionOn a ?_
  intro representative
  exact Subtype.refl representative

theorem le_trans (a b c : QTy leRow) : le a b → le b c → le a c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro first middle last
  exact Subtype.trans

theorem le_antisymm (a b : QTy leRow) : le a b → le b a → a = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro first last forward backward
  exact Quotient.sound ⟨forward, backward⟩

theorem eq_iff_mutual_subtype (a b : QTy leRow) :
    a = b ↔ le a b ∧ le b a := by
  constructor
  · intro equal
    subst b
    exact ⟨le_refl a, le_refl a⟩
  · rintro ⟨forward, backward⟩
    exact le_antisymm a b forward backward

/-- A binary constructor whose semantic congruence has already been proved. -/
def liftBinary (operation : Ty Row → Ty Row → Ty Row)
    (congruent : ∀ {a a' b b'}, Equivalent leRow a a' → Equivalent leRow b b' →
      Equivalent leRow (operation a b) (operation a' b')) :
    QTy leRow → QTy leRow → QTy leRow :=
  Quotient.lift₂ (fun a b => mk (operation a b))
    (fun _ _ _ _ left right => Quotient.sound (congruent left right))

def union : QTy leRow → QTy leRow → QTy leRow :=
  liftBinary Ty.union SemanticRecords.union_congr

def inter : QTy leRow → QTy leRow → QTy leRow :=
  liftBinary Ty.inter SemanticRecords.inter_congr

def pair : QTy leRow → QTy leRow → QTy leRow :=
  liftBinary Ty.pair SemanticRecords.pair_congr

def record (label : Nat) : QTy leRow → QTy leRow → QTy leRow :=
  liftBinary (Ty.record label) (SemanticRecords.record_congr label)

def variant (label : Nat) : QTy leRow → QTy leRow :=
  Quotient.lift (fun payload => mk (.variant label payload))
    (fun _ _ same => Quotient.sound (SemanticRecords.variant_congr label same))

def arrow (rowRefl : ∀ row, leRow row row)
    (input : QTy leRow) (inputRow : Row) (output : QTy leRow) (outputRow : Row) : QTy leRow :=
  liftBinary (fun a b => Ty.arrow a inputRow b outputRow)
    (SemanticRecords.arrow_congr inputRow outputRow (rowRefl inputRow) (rowRefl outputRow))
    input output

@[simp] theorem union_mk (a b : Ty Row) :
    union (mk (leRow := leRow) a) (mk b) = mk (.union a b) := rfl

@[simp] theorem inter_mk (a b : Ty Row) :
    inter (mk (leRow := leRow) a) (mk b) = mk (.inter a b) := rfl

@[simp] theorem pair_mk (a b : Ty Row) :
    pair (mk (leRow := leRow) a) (mk b) = mk (.pair a b) := rfl

@[simp] theorem record_mk (label : Nat) (a b : Ty Row) :
    record label (mk (leRow := leRow) a) (mk b) = mk (.record label a b) := rfl

@[simp] theorem variant_mk (label : Nat) (a : Ty Row) :
    variant label (mk (leRow := leRow) a) = mk (.variant label a) := rfl

@[simp] theorem arrow_mk (rowRefl : ∀ row, leRow row row)
    (input output : Ty Row) (inputRow outputRow : Row) :
    arrow rowRefl (mk input) inputRow (mk output) outputRow =
      mk (.arrow input inputRow output outputRow) := rfl

theorem union_is_join (a b c : QTy leRow) :
    le (union a b) c ↔ le a c ∧ le b c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro first last target
  exact SemanticRecords.union_is_join first last target

theorem inter_is_meet (a b c : QTy leRow) :
    le c (inter a b) ↔ le c a ∧ le c b := by
  refine Quotient.inductionOn₃ a b c ?_
  intro first last source
  exact SemanticRecords.inter_is_meet first last source

theorem bottom_le (a : QTy leRow) : le (mk .bottom) a := by
  refine Quotient.inductionOn a ?_
  exact fun representative => Subtype.bottom representative

theorem le_top (a : QTy leRow) : le a (mk .top) := by
  refine Quotient.inductionOn a ?_
  exact fun representative => Subtype.top representative

@[simp] theorem union_bottom (a : QTy leRow) : union a (mk .bottom) = a := by
  refine Quotient.inductionOn a ?_
  intro representative
  exact Quotient.sound (SemanticRecords.union_bottom_equivalent representative)

@[simp] theorem inter_top (a : QTy leRow) : inter a (mk .top) = a := by
  refine Quotient.inductionOn a ?_
  intro representative
  exact Quotient.sound (SemanticRecords.inter_top_equivalent representative)

/-- Mutual subtype equality in either argument is actual equality of the
record type, with no syntactic record-tail restriction. -/
theorem record_eq_of_mutual_subtype (label : Nat) (value value' rest rest' : QTy leRow)
    (headForward : le value value') (headBackward : le value' value)
    (tailForward : le rest rest') (tailBackward : le rest' rest) :
    record label value rest = record label value' rest' := by
  rw [le_antisymm value value' headForward headBackward,
    le_antisymm rest rest' tailForward tailBackward]

@[simp] theorem record_tail_union_bottom (label : Nat) (value rest : QTy leRow) :
    record label value (union rest (mk .bottom)) = record label value rest := by
  rw [union_bottom]

theorem boundary_pair_equal (label : Nat) (value : Ty Row) :
    mk (leRow := leRow) (.record label value .emptyRecord) =
      mk (.record label value (.union .emptyRecord .bottom)) :=
  Quotient.sound (SemanticRecords.boundary_pair_equivalent label value)

theorem int_not_str : ¬ le (mk (leRow := leRow) (.base .int)) (mk (.base .str)) :=
  SemanticRecords.int_not_str

theorem top_not_int : ¬ le (mk (leRow := leRow) .top) (mk (.base .int)) :=
  SemanticRecords.top_not_int

theorem top_not_bottom : ¬ le (mk (leRow := leRow) .top) (mk .bottom) :=
  SemanticRecords.top_not_bottom

theorem int_ne_str : mk (leRow := leRow) (.base .int) ≠ mk (.base .str) := by
  intro equal
  exact int_not_str ((eq_iff_mutual_subtype _ _).mp equal).1

/-- The quotient model has all original constructors and exactly the same
row carrier and operations. Reflexivity is required only to lift arrows. -/
def model (Row : Type u) (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row) : Model where
  Ty := QTy leRow
  Row := Row
  base := fun base => mk (.base base)
  bottom := mk .bottom
  top := mk .top
  union := union
  inter := inter
  pair := pair
  emptyRecord := mk .emptyRecord
  record := record
  variant := variant
  arrow := arrow rowRefl
  empty := empty
  join := join
  subTy := le
  subRow := leRow

end Yulang.SemanticRecordQuotient
