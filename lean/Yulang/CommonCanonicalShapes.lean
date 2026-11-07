import Yulang.CommonCanonicalOpen
import Yulang.CommonRecord
import Yulang.ProducerCanonicalShapes

/-!
# Fixed-shape canonicalization with arbitrary common type parameters

The executable syntax, code, collection and readback are exactly those of
`ProducerCanonicalShapes`. The interpretation now uses `Common.Ty` for every
shared parameter, including arbitrary masks, default records, arrows and
closed regular blocks. The fixed constructor skeleton may nest pairs, single
required fields, tags and arrows; unions are grouped componentwise.

The code is relative to one known `Shape`: constructor labels and row-slot
IDs are stored there, not repeated in `Code`. Equality is proved only within
that same shape and one fixed row-slot assignment. This is not a standalone
encoding of arbitrary interfaces, and it does not alpha-normalize variables
or identify different row-slot IDs across different shapes.
-/

namespace Yulang.CommonCanonicalShapes

open ProducerCanonicalShapes (Shape Term Bundle Code collect)
open CommonFinite (ProbeAt ProbeStep MaskedProbeStep)

variable {n : Nat}

def instantiate (rows : Nat → Common.Row) (parameters : Fin n → Common.Ty) :
    {shape : Shape} → Term n shape → Common.Ty
  | _, .scalar expression => CommonCanonicalOpen.instantiate parameters expression
  | _, .pair first last => Common.pair (instantiate rows parameters first) (instantiate rows parameters last)
  | _, .required label payload => Common.required label (instantiate rows parameters payload)
  | _, .variant label payload => Common.variant label (instantiate rows parameters payload)
  | _, .arrow incoming outgoing input output =>
      Common.arrow (CommonCanonicalOpen.instantiate parameters input) (rows incoming)
        (instantiate rows parameters output) (rows outgoing)
  | _, .union first last => .union (instantiate rows parameters first) (instantiate rows parameters last)

def instantiateBundle (rows : Nat → Common.Row) (parameters : Fin n → Common.Ty) :
    (shape : Shape) → Bundle n shape → Common.Ty
  | .scalar, expression => CommonCanonicalOpen.instantiate parameters expression
  | .pair first last, fields =>
      Common.pair (instantiateBundle rows parameters first fields.1) (instantiateBundle rows parameters last fields.2)
  | .required label payload, fields => Common.required label (instantiateBundle rows parameters payload fields)
  | .variant label payload, fields => Common.variant label (instantiateBundle rows parameters payload fields)
  | .arrow incoming outgoing result, fields =>
      Common.arrow (CommonCanonicalOpen.instantiate parameters fields.1) (rows incoming)
        (instantiateBundle rows parameters result fields.2) (rows outgoing)

theorem equivalent_iff_probes (first last : Common.Ty) :
    Common.Equivalent first last ↔
      ∀ depth rank environment observation,
        ProbeAt Common.rowLe rank environment (Common.observeTy depth first) observation ↔
          ProbeAt Common.rowLe rank environment (Common.observeTy depth last) observation := by
  constructor
  · intro same depth
    exact (CommonFinite.producerEq_iff_probe _ _).mp ⟨same.1 depth, same.2 depth⟩
  · intro same
    constructor <;> intro depth
    · exact ((CommonFinite.producerEq_iff_probe _ _).mpr (same depth)).1
    · exact ((CommonFinite.producerEq_iff_probe _ _).mpr (same depth)).2

theorem pair_union_group (a b c d : Common.Ty) :
    Common.Equivalent (.union (Common.pair a b) (Common.pair c d))
      (Common.pair (.union a c) (.union b d)) := by
  apply (equivalent_iff_probes _ _).mpr
  intro depth rank environment observation
  cases depth <;> cases rank <;> cases observation <;>
    simp [Common.pair, Common.observeTy, CommonSyntax.Layer.evalAt,
      CommonSyntax.observe, CommonSyntax.graph, ProbeAt, ProbeStep, MaskedProbeStep]

theorem required_union_group (label : Nat) (first last : Common.Ty) :
    Common.Equivalent (.union (Common.required label first) (Common.required label last))
      (Common.required label (.union first last)) := by
  apply (equivalent_iff_probes _ _).mpr
  intro depth rank environment observation
  cases depth <;> cases rank <;> cases observation <;>
    simp [Common.required, Common.record, Common.emptyRecord, Common.observeTy, CommonSyntax.Layer.evalAt,
      CommonSyntax.observe, CommonSyntax.graph, ProbeAt, ProbeStep, MaskedProbeStep, and_assoc, and_left_comm]
  all_goals split <;> simp

theorem variant_union_group (label : Nat) (first last : Common.Ty) :
    Common.Equivalent (.union (Common.variant label first) (Common.variant label last))
      (Common.variant label (.union first last)) := by
  apply (equivalent_iff_probes _ _).mpr
  intro depth rank environment observation
  cases depth <;> cases rank <;> cases observation <;>
    simp [Common.variant, Common.observeTy, CommonSyntax.Layer.evalAt,
      CommonSyntax.observe, CommonSyntax.graph, ProbeAt, ProbeStep, MaskedProbeStep, and_assoc, and_left_comm]

theorem arrow_union_group (input input' output output' : Common.Ty) (incoming outgoing : Common.Row) :
    Common.Equivalent
      (.union (Common.arrow input incoming output outgoing) (Common.arrow input' incoming output' outgoing))
      (Common.arrow (.inter input input') incoming (.union output output') outgoing) := by
  apply (equivalent_iff_probes _ _).mpr
  intro depth rank environment observation
  cases depth <;> cases rank <;> cases observation <;>
    simp [Common.arrow, Common.observeTy, CommonSyntax.Layer.evalAt, CommonSyntax.observe,
      CommonSyntax.graph, ProbeAt, ProbeStep, MaskedProbeStep, or_imp, forall_and]

theorem pair_equivalent_iff (a b c d : Common.Ty) :
    Common.Equivalent (Common.pair a b) (Common.pair c d) ↔
      Common.Equivalent a c ∧ Common.Equivalent b d := by
  have forward := Common.common_pair_iff a b c d
  have backward := Common.common_pair_iff c d a b
  simp only [Common.model] at forward backward
  simp only [Common.Equivalent, forward, backward, and_assoc, and_left_comm]

theorem required_equivalent_iff (label : Nat) (first last : Common.Ty) :
    Common.Equivalent (Common.required label first) (Common.required label last) ↔
      Common.Equivalent first last := by
  change (Common.Subtype (Common.record label first Common.emptyRecord) (Common.required label last) ∧
    Common.Subtype (Common.record label last Common.emptyRecord) (Common.required label first)) ↔ _
  simp only [Common.common_singleton_requirement_iff, Common.Equivalent]

theorem variant_equivalent_iff (label : Nat) (first last : Common.Ty) :
    Common.Equivalent (Common.variant label first) (Common.variant label last) ↔
      Common.Equivalent first last := by
  have forward := Common.common_variant_iff label first last
  have backward := Common.common_variant_iff label last first
  simp only [Common.model] at forward backward
  simp only [Common.Equivalent, forward, backward]

theorem arrow_equivalent_iff (input input' output output' : Common.Ty) (incoming outgoing : Common.Row) :
    Common.Equivalent (Common.arrow input incoming output outgoing) (Common.arrow input' incoming output' outgoing) ↔
      Common.Equivalent input input' ∧ Common.Equivalent output output' := by
  have forward := Common.common_arrow_iff input input' output output' incoming incoming outgoing outgoing
  have backward := Common.common_arrow_iff input' input output' output incoming incoming outgoing outgoing
  simp only [Common.model] at forward backward
  simp only [Common.Equivalent, forward, backward, Common.rowLe_refl,
    true_and, and_assoc, and_left_comm, and_comm]

theorem union_congr {first last first' last' : Common.Ty}
    (left : Common.Equivalent first first') (right : Common.Equivalent last last') :
    Common.Equivalent (.union first last) (.union first' last') :=
  ⟨Common.common_union_mono left.1 right.1, Common.common_union_mono left.2 right.2⟩

theorem bundle_join_equivalent (rows : Nat → Common.Row) (parameters : Fin n → Common.Ty)
    (shape : Shape) (first last : Bundle n shape) :
    Common.Equivalent (instantiateBundle rows parameters shape (Bundle.join shape first last))
      (.union (instantiateBundle rows parameters shape first) (instantiateBundle rows parameters shape last)) := by
  induction shape with
  | scalar => exact Common.equivalent_refl _
  | pair left right ihl ihr =>
      exact Common.equivalent_trans ((pair_equivalent_iff _ _ _ _).mpr ⟨ihl first.1 last.1, ihr first.2 last.2⟩)
        (Common.equivalent_symm (pair_union_group _ _ _ _))
  | required label payload ih =>
      exact Common.equivalent_trans ((required_equivalent_iff label _ _).mpr (ih first last))
        (Common.equivalent_symm (required_union_group label _ _))
  | variant label payload ih =>
      exact Common.equivalent_trans ((variant_equivalent_iff label _ _).mpr (ih first last))
        (Common.equivalent_symm (variant_union_group label _ _))
  | arrow incoming outgoing result ih =>
      exact Common.equivalent_trans ((arrow_equivalent_iff _ _ _ _ (rows incoming) (rows outgoing)).mpr
        ⟨Common.equivalent_refl _, ih first.2 last.2⟩)
        (Common.equivalent_symm (arrow_union_group _ _ _ _ (rows incoming) (rows outgoing)))

theorem collect_equivalent (rows : Nat → Common.Row) (parameters : Fin n → Common.Ty)
    {shape : Shape} (expression : Term n shape) :
    Common.Equivalent (instantiateBundle rows parameters shape (collect expression))
      (instantiate rows parameters expression) := by
  induction expression with
  | scalar expression => exact Common.equivalent_refl _
  | pair first last ihf ihl => exact (pair_equivalent_iff _ _ _ _).mpr ⟨ihf, ihl⟩
  | required label payload ih => exact (required_equivalent_iff label _ _).mpr ih
  | variant label payload ih => exact (variant_equivalent_iff label _ _).mpr ih
  | arrow incoming outgoing input output ih =>
      exact (arrow_equivalent_iff _ _ _ _ (rows incoming) (rows outgoing)).mpr ⟨Common.equivalent_refl _, ih⟩
  | union first last ihf ihl =>
      exact Common.equivalent_trans (bundle_join_equivalent rows parameters _ _ _) (union_congr ihf ihl)

theorem bundle_code_exact (rows : Nat → Common.Row) (shape : Shape) (first last : Bundle n shape) :
    (∀ parameters : Fin n → Common.Ty,
      Common.Equivalent (instantiateBundle rows parameters shape first) (instantiateBundle rows parameters shape last)) ↔
      Bundle.encode shape first = Bundle.encode shape last := by
  induction shape with
  | scalar => exact CommonCanonicalOpen.canonicalEncoding_exact first last
  | pair left right ihl ihr =>
      simp only [instantiateBundle, pair_equivalent_iff, forall_and, Bundle.encode, Code, Prod.mk.injEq]
      exact and_congr (ihl first.1 last.1) (ihr first.2 last.2)
  | required label payload ih =>
      simp only [instantiateBundle, required_equivalent_iff, Bundle.encode]
      exact ih first last
  | variant label payload ih =>
      simp only [instantiateBundle, variant_equivalent_iff, Bundle.encode]
      exact ih first last
  | arrow incoming outgoing result ih =>
      simp only [instantiateBundle, arrow_equivalent_iff, forall_and, Bundle.encode, Code, Prod.mk.injEq]
      exact and_congr (CommonCanonicalOpen.canonicalEncoding_exact first.1 last.1) (ih first.2 last.2)

def Equivalent (rows : Nat → Common.Row) {shape : Shape} (first last : Term n shape) : Prop :=
  ∀ parameters : Fin n → Common.Ty,
    Common.Equivalent (instantiate rows parameters first) (instantiate rows parameters last)

abbrev canonicalEncoding := @ProducerCanonicalShapes.canonicalEncoding
abbrev normalize := @ProducerCanonicalShapes.normalize

/-- The same fixed-shape code is complete for every common parameter family.
Rows are arbitrary concrete common rows, held fixed in the shared shape. -/
theorem canonicalEncoding_exact (rows : Nat → Common.Row) {shape : Shape} (first last : Term n shape) :
    Equivalent rows first last ↔ canonicalEncoding first = canonicalEncoding last := by
  change Equivalent rows first last ↔ Bundle.encode shape (collect first) = Bundle.encode shape (collect last)
  rw [← bundle_code_exact rows]
  constructor
  · intro same parameters
    exact Common.equivalent_trans (collect_equivalent rows parameters first)
      (Common.equivalent_trans (same parameters) (Common.equivalent_symm (collect_equivalent rows parameters last)))
  · intro same parameters
    exact Common.equivalent_trans (Common.equivalent_symm (collect_equivalent rows parameters first))
      (Common.equivalent_trans (same parameters) (collect_equivalent rows parameters last))

theorem bundle_readback_equivalent (rows : Nat → Common.Row) (parameters : Fin n → Common.Ty)
    (shape : Shape) (fields : Bundle n shape) :
    Common.Equivalent (instantiate rows parameters (Code.readback shape (Bundle.encode shape fields)))
      (instantiateBundle rows parameters shape fields) := by
  induction shape with
  | scalar => exact CommonCanonicalOpen.normalize_equivalent fields parameters
  | pair first last ihf ihl => exact (pair_equivalent_iff _ _ _ _).mpr ⟨ihf fields.1, ihl fields.2⟩
  | required label payload ih => exact (required_equivalent_iff label _ _).mpr (ih fields)
  | variant label payload ih => exact (variant_equivalent_iff label _ _).mpr (ih fields)
  | arrow incoming outgoing result ih =>
      exact (arrow_equivalent_iff _ _ _ _ (rows incoming) (rows outgoing)).mpr
        ⟨CommonCanonicalOpen.normalize_equivalent fields.1 parameters, ih fields.2⟩

theorem normalize_equivalent (rows : Nat → Common.Row) {shape : Shape} (expression : Term n shape) :
    Equivalent rows (normalize expression) expression := by
  intro parameters
  exact Common.equivalent_trans (bundle_readback_equivalent rows parameters _ _)
    (collect_equivalent rows parameters expression)

theorem normalize_exact (rows : Nat → Common.Row) {shape : Shape} (first last : Term n shape) :
    Equivalent rows first last ↔ normalize first = normalize last := by
  constructor
  · intro same
    exact congrArg (Code.readback shape) ((canonicalEncoding_exact rows first last).mp same)
  · intro same parameters
    have hf := normalize_equivalent rows first parameters
    have hl := normalize_equivalent rows last parameters
    rw [same] at hf
    exact Common.equivalent_trans (Common.equivalent_symm hf) hl

theorem normalize_idempotent {shape : Shape} (expression : Term n shape) :
    normalize (normalize expression) = normalize expression := ProducerCanonicalShapes.normalize_idempotent expression

end Yulang.CommonCanonicalShapes
