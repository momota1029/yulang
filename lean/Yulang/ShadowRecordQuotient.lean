import Yulang.ShadowSemanticRecords
import Yulang.SemanticRecordQuotient
import Yulang.RigidRecordQuotient

/-!
# Semantic quotient after hidden-field erasure

The quotient identifies mutual subtypes of the independently defined
`ShadowSemanticRecords` relation. All constructors descend to it, and the
new hidden-field equation becomes actual equality for every quotient tail.
Existing decision-38 and decision-39 quotients map into it without losing
any previous comparisons. This module does not supply a ground checker.
-/

namespace Yulang.ShadowRecordQuotient

open Inference
open StructuralBase (Ty)
open ShadowSemanticRecords (Subtype Equivalent)

universe u

variable {Row : Type u}

def typeSetoid (leRow : Row → Row → Prop) : Setoid (Ty Row) where
  r := Equivalent leRow
  iseqv := ⟨Equivalent.refl, Equivalent.symm, Equivalent.trans⟩

abbrev QTy (leRow : Row → Row → Prop) := Quotient (typeSetoid leRow)

variable {leRow : Row → Row → Prop}

def mk (type : Ty Row) : QTy leRow := Quotient.mk (typeSetoid leRow) type

/-- The previous semantic identification is retained when hidden-field
equality is added. This map does not assert reflection of the old order. -/
def fromCongruence : SemanticRecordQuotient.QTy leRow → QTy leRow :=
  Quotient.lift mk (fun _ _ same => Quotient.sound
    ⟨ShadowSemanticRecords.semantic_subtype same.1,
      ShadowSemanticRecords.semantic_subtype same.2⟩)

@[simp] theorem fromCongruence_mk (type : Ty Row) :
    fromCongruence (SemanticRecordQuotient.mk (leRow := leRow) type) = mk type := rfl

/-- Decision-39 types map into the extended quotient. -/
def fromRigid : RigidRecordQuotient.QTy leRow → QTy leRow :=
  Quotient.lift mk (fun _ _ same => Quotient.sound
    ⟨ShadowSemanticRecords.rigid_subtype same.1,
      ShadowSemanticRecords.rigid_subtype same.2⟩)

@[simp] theorem fromRigid_mk (type : Ty Row) :
    fromRigid (RigidRecordQuotient.mk (leRow := leRow) type) = mk type := rfl

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
  liftBinary Ty.union ShadowSemanticRecords.union_congr

def inter : QTy leRow → QTy leRow → QTy leRow :=
  liftBinary Ty.inter ShadowSemanticRecords.inter_congr

def pair : QTy leRow → QTy leRow → QTy leRow :=
  liftBinary Ty.pair ShadowSemanticRecords.pair_congr

def record (label : Nat) : QTy leRow → QTy leRow → QTy leRow :=
  liftBinary (Ty.record label) (ShadowSemanticRecords.record_congr label)

def variant (label : Nat) : QTy leRow → QTy leRow :=
  Quotient.lift (fun payload => mk (.variant label payload))
    (fun _ _ same => Quotient.sound (ShadowSemanticRecords.variant_congr label same))

def arrow (rowRefl : ∀ row, leRow row row)
    (input : QTy leRow) (inputRow : Row) (output : QTy leRow) (outputRow : Row) : QTy leRow :=
  liftBinary (fun a b => Ty.arrow a inputRow b outputRow)
    (ShadowSemanticRecords.arrow_congr inputRow outputRow (rowRefl inputRow) (rowRefl outputRow))
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
  exact ShadowSemanticRecords.union_is_join first last target

theorem inter_is_meet (a b c : QTy leRow) :
    le c (inter a b) ↔ le c a ∧ le c b := by
  refine Quotient.inductionOn₃ a b c ?_
  intro first last source
  exact ShadowSemanticRecords.inter_is_meet first last source

theorem bottom_le (a : QTy leRow) : le (mk .bottom) a := by
  refine Quotient.inductionOn a ?_
  exact fun representative => Subtype.bottom representative

theorem le_top (a : QTy leRow) : le a (mk .top) := by
  refine Quotient.inductionOn a ?_
  exact fun representative => Subtype.top representative

@[simp] theorem union_bottom (a : QTy leRow) : union a (mk .bottom) = a := by
  refine Quotient.inductionOn a ?_
  intro representative
  exact Quotient.sound (ShadowSemanticRecords.union_bottom_equivalent representative)

@[simp] theorem inter_top (a : QTy leRow) : inter a (mk .top) = a := by
  refine Quotient.inductionOn a ?_
  intro representative
  exact Quotient.sound (ShadowSemanticRecords.inter_top_equivalent representative)

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
  Quotient.sound (ShadowSemanticRecords.boundary_pair_equivalent label value)

/-- Decision 40 holds for arbitrary semantic tails, not just proper spines. -/
@[simp] theorem shadow (label : Nat) (visible hidden rest : QTy leRow) :
    record label visible (record label hidden rest) = record label visible rest := by
  refine Quotient.inductionOn₃ visible hidden rest ?_
  intro a b r
  exact Quotient.sound (ShadowSemanticRecords.shadow_equivalent label a b r)

theorem hidden_payload_irrelevant (label : Nat)
    (visible first last rest : QTy leRow) :
    record label visible (record label first rest) =
      record label visible (record label last rest) := by
  rw [shadow, shadow]

/-- Rigidity is existence of a proper-spine representative, so it is a
property of the semantic type rather than of a particular spelling. -/
def Rigid (type : QTy leRow) : Prop :=
  ∃ representative : Ty Row, StructuralBase.IsRecord representative ∧ mk representative = type

theorem rigid_empty : Rigid (mk (leRow := leRow) .emptyRecord) :=
  ⟨.emptyRecord, .empty, rfl⟩

theorem rigid_record (label : Nat) (head tail : QTy leRow) (shape : Rigid tail) :
    Rigid (record label head tail) := by
  obtain ⟨rest, proper, rfl⟩ := shape
  refine Quotient.inductionOn head ?_
  intro value
  exact ⟨.record label value rest, .field proper, rfl⟩

/-- The preserved decision-39 rule on the quotient. Only the demanded tail must have a rigid
representative; no general one-way covariance is asserted. -/
theorem record_tail_mono (label : Nat) (head source target : QTy leRow)
    (rigid : Rigid target) (below : le source target) :
    le (record label head source) (record label head target) := by
  obtain ⟨rest, shape, rfl⟩ := rigid
  revert below
  refine Quotient.inductionOn₂ head source ?_
  intro value original below
  exact ShadowSemanticRecords.Subtype.recordTail shape below

theorem record_head (label : Nat) (head tail : QTy leRow)
    (admissible : le tail (mk .emptyRecord)) :
    le (record label head tail) (record label head (mk .emptyRecord)) :=
  record_tail_mono label head tail (mk .emptyRecord) rigid_empty admissible

theorem record_width (label : Nat) (head tail : QTy leRow)
    (admissible : le tail (mk .emptyRecord)) :
    le (record label head tail) (mk .emptyRecord) := by
  revert admissible
  refine Quotient.inductionOn₂ head tail ?_
  intro value rest admissible
  exact ShadowSemanticRecords.record_width label value admissible

theorem record_never_below_empty (label : Nat) (head : QTy leRow) :
    le (record label head (mk .bottom)) (mk .emptyRecord) :=
  record_width label head (mk .bottom) (bottom_le _)

theorem int_not_str : ¬ le (mk (leRow := leRow) (.base .int)) (mk (.base .str)) :=
  ShadowSemanticRecords.int_not_str

theorem top_not_int : ¬ le (mk (leRow := leRow) .top) (mk (.base .int)) :=
  ShadowSemanticRecords.top_not_int

theorem top_not_bottom : ¬ le (mk (leRow := leRow) .top) (mk .bottom) :=
  ShadowSemanticRecords.top_not_bottom

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

end Yulang.ShadowRecordQuotient
