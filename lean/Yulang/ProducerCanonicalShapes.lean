import Yulang.ProducerCanonicalOpenClauses
import Yulang.ProducerContextualRecord

/-!
# Exact constructor grouping for declared finite shapes

The expression grammar fixes the constructor shape while allowing unions at
every positive node and arbitrary shared scalar-lattice expressions at leaves.
Pairs, tags and single required fields may nest. Arrows have a scalar-lattice
domain and explicitly shared input/output row-slot IDs; their unions group the
domains by intersection and their results by union. Parameter instances are
still arbitrary contextual types, so a domain variable can itself denote a
function or record.

The shape restriction is explicit syntax, not solver success. This module
does not canonicalize mixed constructor heads, arrows with differing row slots,
general record spines, nominal declarations, role predicates or regular graphs.
-/

namespace Yulang.ProducerCanonicalShapes

open Inference (Base)
open StructuralBase (Ty)
open ProducerContextual

namespace Scalar
abbrev Expr := ProducerCanonicalOpen.Expr
abbrev Code (n : Nat) := List (List (ProducerCanonicalOpen.Atom n))
abbrev encode := @ProducerCanonicalOpenClauses.canonicalEncoding
abbrev normalize := @ProducerCanonicalOpenClauses.normalize
end Scalar

universe u
variable {n : Nat} {Row : Type u}

inductive Shape where
  | scalar
  | pair : Shape → Shape → Shape
  | required : Nat → Shape → Shape
  | variant : Nat → Shape → Shape
  | arrow : Nat → Nat → Shape → Shape
  deriving DecidableEq, Repr

inductive Term (n : Nat) : Shape → Type where
  | scalar : Scalar.Expr n → Term n .scalar
  | pair : Term n first → Term n last → Term n (.pair first last)
  | required (label : Nat) : Term n payload → Term n (.required label payload)
  | variant (label : Nat) : Term n payload → Term n (.variant label payload)
  | arrow (incoming outgoing : Nat) : Scalar.Expr n → Term n result → Term n (.arrow incoming outgoing result)
  | union : Term n shape → Term n shape → Term n shape

def Bundle (n : Nat) : Shape → Type
  | .scalar => Scalar.Expr n
  | .pair first last => Bundle n first × Bundle n last
  | .required _ payload | .variant _ payload => Bundle n payload
  | .arrow _ _ result => Scalar.Expr n × Bundle n result

def Code (n : Nat) : Shape → Type
  | .scalar => Scalar.Code n
  | .pair first last => Code n first × Code n last
  | .required _ payload | .variant _ payload => Code n payload
  | .arrow _ _ result => Scalar.Code n × Code n result

def Term.embed (rows : Nat → Row) (parameters : Fin n → Ty Row) :
    {shape : Shape} → Term n shape → Ty Row
  | _, .scalar expression => expression.embed parameters
  | _, .pair first last => .pair (first.embed rows parameters) (last.embed rows parameters)
  | _, .required label payload => .record label (payload.embed rows parameters) .emptyRecord
  | _, .variant label payload => .variant label (payload.embed rows parameters)
  | _, .arrow incoming outgoing input output =>
      .arrow (input.embed parameters) (rows incoming) (output.embed rows parameters) (rows outgoing)
  | _, .union first last => .union (first.embed rows parameters) (last.embed rows parameters)

def Bundle.embed (rows : Nat → Row) (parameters : Fin n → Ty Row) :
    (shape : Shape) → Bundle n shape → Ty Row
  | .scalar, expression => ProducerCanonicalOpen.Expr.embed parameters expression
  | .pair first last, fields => .pair (embed rows parameters first fields.1) (embed rows parameters last fields.2)
  | .required label payload, fields => .record label (embed rows parameters payload fields) .emptyRecord
  | .variant label payload, fields => .variant label (embed rows parameters payload fields)
  | .arrow incoming outgoing result, fields =>
      .arrow (ProducerCanonicalOpen.Expr.embed parameters fields.1)
        (rows incoming) (embed rows parameters result fields.2) (rows outgoing)

def Bundle.join : (shape : Shape) → Bundle n shape → Bundle n shape → Bundle n shape
  | .scalar, first, last => .union first last
  | .pair left right, first, last => (join left first.1 last.1, join right first.2 last.2)
  | .required _ payload, first, last | .variant _ payload, first, last => join payload first last
  | .arrow _ _ result, first, last => (.inter first.1 last.1, join result first.2 last.2)

def collect : {shape : Shape} → Term n shape → Bundle n shape
  | _, .scalar expression => expression
  | _, .pair first last => (collect first, collect last)
  | .required _ child, .required _ payload => collect (shape := child) payload
  | .variant _ child, .variant _ payload => collect (shape := child) payload
  | _, .arrow _ _ input output => (input, collect output)
  | shape, .union first last => Bundle.join shape (collect first) (collect last)

theorem required_union_group (leRow : Row → Row → Prop) (label : Nat) (first last : Ty Row) :
    ProducerEq leRow (.union (.record label first .emptyRecord) (.record label last .emptyRecord))
      (.record label (.union first last) .emptyRecord) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank env observation
  cases rank <;> cases observation <;> simp [ProbeAt, ProbeStep, and_assoc, and_left_comm]

/-- The two row slots are identical, but both domain expressions and both
result expressions are arbitrary contextual types. -/
theorem arrow_union_group (leRow : Row → Row → Prop)
    (input input' output output' : Ty Row) (incoming outgoing : Row) :
    ProducerEq leRow
      (.union (.arrow input incoming output outgoing) (.arrow input' incoming output' outgoing))
      (.arrow (.inter input input') incoming (.union output output') outgoing) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank env observation
  cases rank <;> cases observation <;>
    simp [ProbeAt, ProbeStep, probeAt_inter, or_imp, forall_and]

theorem bundle_join_equivalent (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rows : Nat → Row) (parameters : Fin n → Ty Row) (shape : Shape)
    (first last : Bundle n shape) :
    ProducerEq leRow (Bundle.embed rows parameters shape (Bundle.join shape first last))
      (.union (Bundle.embed rows parameters shape first) (Bundle.embed rows parameters shape last)) := by
  induction shape with
  | scalar => exact producerEq_refl _
  | pair left right ihl ihr =>
      exact producerEq_trans (producerEq_pair (ihl first.1 last.1) (ihr first.2 last.2))
        (producerEq_symm (pair_union_group _ _ _ _))
  | required label payload ih =>
      exact producerEq_trans (producerEq_record label (ih first last) (producerEq_refl .emptyRecord))
        (producerEq_symm (required_union_group leRow label _ _))
  | variant label payload ih =>
      exact producerEq_trans (producerEq_variant label (ih first last)) (variant_union label _ _)
  | arrow incoming outgoing result ih =>
      exact producerEq_trans
        (producerEq_arrow rowRefl rowTrans (rows incoming) (rows outgoing) (producerEq_refl _)
          (ih first.2 last.2))
        (producerEq_symm (arrow_union_group leRow _ _ _ _ (rows incoming) (rows outgoing)))

theorem collect_equivalent (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rows : Nat → Row) (parameters : Fin n → Ty Row) {shape : Shape} (expression : Term n shape) :
    ProducerEq leRow (Bundle.embed rows parameters shape (collect expression)) (expression.embed rows parameters) := by
  induction expression with
  | scalar expression => exact producerEq_refl _
  | pair first last ihf ihl => exact producerEq_pair ihf ihl
  | required label payload ih => exact producerEq_record label ih (producerEq_refl .emptyRecord)
  | variant label payload ih => exact producerEq_variant label ih
  | arrow incoming outgoing input output ih =>
      exact producerEq_arrow rowRefl rowTrans (rows incoming) (rows outgoing) (producerEq_refl _) ih
  | union first last ihf ihl =>
      exact producerEq_trans (bundle_join_equivalent leRow rowRefl rowTrans rows parameters _ _ _)
        (producerEq_union ihf ihl)

def Bundle.encode : (shape : Shape) → Bundle n shape → Code n shape
  | .scalar, expression => Scalar.encode expression
  | .pair first last, fields => (encode first fields.1, encode last fields.2)
  | .required _ payload, fields | .variant _ payload, fields => encode payload fields
  | .arrow _ _ result, fields => (Scalar.encode fields.1, encode result fields.2)

def canonicalEncoding {shape : Shape} (expression : Term n shape) : Code n shape :=
  Bundle.encode shape (collect expression)

def Equivalent (leRow : Row → Row → Prop) (rows : Nat → Row)
    {shape : Shape} (first last : Term n shape) : Prop :=
  ∀ parameters : Fin n → Ty Row,
    ProducerEq leRow (first.embed rows parameters) (last.embed rows parameters)

theorem pair_equivalent_iff (leRow : Row → Row → Prop) (a b c d : Ty Row) :
    ProducerEq leRow (.pair a b) (.pair c d) ↔
      ProducerEq leRow a c ∧ ProducerEq leRow b d := by
  simp only [ProducerEq, producerLe_pair_iff, and_assoc, and_left_comm]

theorem required_equivalent_iff (leRow : Row → Row → Prop) (label : Nat) (a b : Ty Row) :
    ProducerEq leRow (.record label a .emptyRecord) (.record label b .emptyRecord) ↔
      ProducerEq leRow a b := by
  simp only [ProducerEq, ProducerContextualRecord.singleton_requirement_iff]

theorem variant_equivalent_iff (leRow : Row → Row → Prop) (label : Nat) (a b : Ty Row) :
    ProducerEq leRow (.variant label a) (.variant label b) ↔ ProducerEq leRow a b := by
  simp only [ProducerEq, producerLe_variant_iff]

theorem arrow_equivalent_iff (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (input input' output output' : Ty Row) (incoming outgoing : Row) :
    ProducerEq leRow (.arrow input incoming output outgoing)
      (.arrow input' incoming output' outgoing) ↔
      ProducerEq leRow input input' ∧ ProducerEq leRow output output' := by
  simp only [ProducerEq, producerLe_arrow_iff rowRefl rowTrans, rowRefl,
    true_and, and_assoc, and_left_comm, and_comm]

/-- Each scalar slot retains its own universal parameter interpretation. The
row relation may be any preorder; no totality, antisymmetry or solver is used. -/
theorem bundle_code_exact (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rows : Nat → Row) (shape : Shape) (first last : Bundle n shape) :
    (∀ parameters : Fin n → Ty Row,
      ProducerEq leRow (Bundle.embed rows parameters shape first)
        (Bundle.embed rows parameters shape last)) ↔
      Bundle.encode shape first = Bundle.encode shape last := by
  induction shape with
  | scalar => exact ProducerCanonicalOpenClauses.canonicalEncoding_exact leRow first last
  | pair left right ihl ihr =>
      simp only [Bundle.embed, pair_equivalent_iff, forall_and, Bundle.encode, Code, Prod.mk.injEq]
      exact and_congr (ihl first.1 last.1) (ihr first.2 last.2)
  | required label payload ih =>
      simp only [Bundle.embed, required_equivalent_iff, Bundle.encode]
      exact ih first last
  | variant label payload ih =>
      simp only [Bundle.embed, variant_equivalent_iff, Bundle.encode]
      exact ih first last
  | arrow incoming outgoing result ih =>
      simp only [Bundle.embed, arrow_equivalent_iff leRow rowRefl rowTrans, forall_and,
        Bundle.encode, Code, Prod.mk.injEq]
      exact and_congr (ProducerCanonicalOpenClauses.canonicalEncoding_exact leRow first.1 last.1)
        (ih first.2 last.2)

/-- Exactness for every expression of the declared finite shape, all shared
parameter instances, all fixed row-slot assignments and every row preorder. -/
theorem canonicalEncoding_exact (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rows : Nat → Row) {shape : Shape} (first last : Term n shape) :
    Equivalent leRow rows first last ↔ canonicalEncoding first = canonicalEncoding last := by
  rw [canonicalEncoding, canonicalEncoding, ← bundle_code_exact leRow rowRefl rowTrans rows]
  constructor
  · intro same parameters
    exact producerEq_trans (collect_equivalent leRow rowRefl rowTrans rows parameters first)
      (producerEq_trans (same parameters)
        (producerEq_symm (collect_equivalent leRow rowRefl rowTrans rows parameters last)))
  · intro same parameters
    exact producerEq_trans (producerEq_symm (collect_equivalent leRow rowRefl rowTrans rows parameters first))
      (producerEq_trans (same parameters)
        (collect_equivalent leRow rowRefl rowTrans rows parameters last))

/-- The code is printed back without a union between matching constructors.
Scalar disjunctions and conjunctions use the ordered minimal-clause readback. -/
def Code.readback : (shape : Shape) → Code n shape → Term n shape
  | .scalar, code => .scalar (ProducerCanonicalOpenClauses.readback code)
  | .pair first last, code => .pair (readback first code.1) (readback last code.2)
  | .required label payload, code => .required label (readback payload code)
  | .variant label payload, code => .variant label (readback payload code)
  | .arrow incoming outgoing result, code =>
      .arrow incoming outgoing (ProducerCanonicalOpenClauses.readback code.1) (readback result code.2)

def normalize {shape : Shape} (expression : Term n shape) : Term n shape :=
  Code.readback shape (canonicalEncoding expression)

theorem normalize_pair_union {left right : Shape}
    (a c : Term n left) (b d : Term n right) :
    normalize (.union (.pair a b) (.pair c d)) =
      .pair (normalize (.union a c)) (normalize (.union b d)) := rfl

theorem normalize_required_union (label : Nat) {payload : Shape} (first last : Term n payload) :
    normalize (.union (.required label first) (.required label last)) =
      .required label (normalize (.union first last)) := rfl

theorem normalize_variant_union (label : Nat) {payload : Shape} (first last : Term n payload) :
    normalize (.union (.variant label first) (.variant label last)) =
      .variant label (normalize (.union first last)) := rfl

/-- The domain is contravariant, so its grouped operation is intersection.
This is an equality of the executable normalizer on arbitrary domain syntax. -/
theorem normalize_arrow_union (incoming outgoing : Nat) {result : Shape}
    (input input' : Scalar.Expr n) (output output' : Term n result) :
    normalize (.union (.arrow incoming outgoing input output) (.arrow incoming outgoing input' output')) =
      .arrow incoming outgoing (Scalar.normalize (.inter input input')) (normalize (.union output output')) := rfl

theorem bundle_readback_equivalent (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rows : Nat → Row) (parameters : Fin n → Ty Row) (shape : Shape) (fields : Bundle n shape) :
    ProducerEq leRow ((Code.readback shape (Bundle.encode shape fields)).embed rows parameters)
      (Bundle.embed rows parameters shape fields) := by
  induction shape with
  | scalar => exact ProducerCanonicalOpenClauses.normalize_equivalent leRow fields parameters
  | pair first last ihf ihl => exact producerEq_pair (ihf fields.1) (ihl fields.2)
  | required label payload ih => exact producerEq_record label (ih fields) (producerEq_refl .emptyRecord)
  | variant label payload ih => exact producerEq_variant label (ih fields)
  | arrow incoming outgoing result ih =>
      exact producerEq_arrow rowRefl rowTrans (rows incoming) (rows outgoing)
        (ProducerCanonicalOpenClauses.normalize_equivalent leRow fields.1 parameters) (ih fields.2)

theorem normalize_equivalent (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rows : Nat → Row) {shape : Shape} (expression : Term n shape) :
    Equivalent leRow rows (normalize expression) expression := by
  intro parameters
  exact producerEq_trans (bundle_readback_equivalent leRow rowRefl rowTrans rows parameters _ _)
    (collect_equivalent leRow rowRefl rowTrans rows parameters expression)

theorem normalize_exact (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rows : Nat → Row) {shape : Shape} (first last : Term n shape) :
    Equivalent leRow rows first last ↔ normalize first = normalize last := by
  constructor
  · intro same
    exact congrArg (Code.readback shape) ((canonicalEncoding_exact leRow rowRefl rowTrans rows first last).mp same)
  · intro same parameters
    have hf := normalize_equivalent leRow rowRefl rowTrans rows first parameters
    have hl := normalize_equivalent leRow rowRefl rowTrans rows last parameters
    rw [same] at hf
    exact producerEq_trans (producerEq_symm hf) hl

theorem normalize_idempotent {shape : Shape} (expression : Term n shape) :
    normalize (normalize expression) = normalize expression :=
  (normalize_exact (Row := Unit) (fun _ _ => True) (fun _ => True.intro)
    (fun _ _ => True.intro) (fun _ => ()) _ _).mp
      (normalize_equivalent (Row := Unit) (fun _ _ => True) (fun _ => True.intro)
        (fun _ _ => True.intro) (fun _ => ()) expression)

namespace Examples

def integer : Term 0 .scalar := .scalar (.atom (.base .int))
def string : Term 0 .scalar := .scalar (.atom (.base .str))

theorem pair_components_group :
    normalize (.union (.pair integer integer) (.pair integer string)) =
      .pair integer (.scalar (.union (.atom (.base .int)) (.atom (.base .str)))) := by
  have first : Scalar.encode (n := 0) (.union (.atom (.base .int)) (.atom (.base .int))) =
      [[.base .int]] := by decide +kernel
  have last : Scalar.encode (n := 0) (.union (.atom (.base .int)) (.atom (.base .str))) =
      [[.base .int, .base .str]] := by decide +kernel
  simp only [normalize, canonicalEncoding, collect, Bundle.join, Bundle.encode, Code.readback, integer, string]
  rw [first, last]
  rfl

theorem required_components_group (label : Nat) :
    normalize (.union (.required label string) (.required label integer)) =
      .required label (.scalar (.union (.atom (.base .int)) (.atom (.base .str)))) := by
  have mixed : Scalar.encode (n := 0) (.union (.atom (.base .str)) (.atom (.base .int))) =
      [[.base .int, .base .str]] := by decide +kernel
  simp only [normalize, canonicalEncoding, collect, Bundle.join, Bundle.encode, Code.readback, integer, string]
  rw [mixed]
  rfl

theorem variant_components_group (label : Nat) :
    normalize (.union (.variant label string) (.variant label integer)) =
      .variant label (.scalar (.union (.atom (.base .int)) (.atom (.base .str)))) := by
  have mixed : Scalar.encode (n := 0) (.union (.atom (.base .str)) (.atom (.base .int))) =
      [[.base .int, .base .str]] := by decide +kernel
  simp only [normalize, canonicalEncoding, collect, Bundle.join, Bundle.encode, Code.readback, integer, string]
  rw [mixed]
  rfl

end Examples

end Yulang.ProducerCanonicalShapes
