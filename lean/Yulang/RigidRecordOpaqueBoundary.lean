import Yulang.RigidRecordAtomNormal
import Yulang.RigidRecordDemands

/-!
# First-field-wins at rigid demands and the boundary at opaque demands

Decision 39 admits an exact comparison which ignores hidden fields when the
demanded record is rigid. The first theorem below proves this for every raw
tail, including arbitrary joins and intersections, without any row laws.

The minimal declarative relation nevertheless distinguishes some raw records
having identical comparisons against every rigid record. Such records are
not semantically rigid representatives themselves. The concrete tails below
are `never` and an admissible union of two ordinary record types.

These are boundaries of extending the rigid-demand erasure to arbitrary raw
demands. They are not source-program rejection results, a proof that a solver
cannot exist, or a new semantic equation for record construction.
-/

namespace Yulang.RigidRecordOpaqueBoundary

open StructuralBase (Ty IsRecord)
open RigidSemanticRecords (Subtype Equivalent)
open RigidRecordAtoms (Atomic)
open RigidRecordViews (View)

universe u

variable {Row : Type u} {leRow : Row → Row → Prop}

/-- An arbitrary hidden field can be removed when comparing against any
rigid demand. Neither admissibility nor a shape restriction on the raw tail
is a premise of this equivalence. -/
theorem hidden_field_rigid_comparison (label : Nat) (visible hidden rest : Ty Row)
    {target : Ty Row} (rigid : IsRecord target) :
    Subtype leRow (.record label visible (.record label hidden rest)) target ↔
      Subtype leRow (.record label visible rest) target := by
  rw [RigidRecordDemands.subtype_iff_fits _ rigid,
    RigidRecordDemands.subtype_iff_fits _ rigid]
  simp [RigidRecordDemands.Fits]

theorem hidden_payload_rigid_comparison (label : Nat)
    (visible first last rest : Ty Row) {target : Ty Row} (rigid : IsRecord target) :
    Subtype leRow (.record label visible (.record label first rest)) target ↔
      Subtype leRow (.record label visible (.record label last rest)) target :=
  (hidden_field_rigid_comparison label visible first rest rigid).trans
    (hidden_field_rigid_comparison label visible last rest rigid).symm

/-- There is no equivalent proper-spine representative. This semantic
predicate is stronger than failure of the raw syntactic `IsRecord` test. -/
def OpaqueTail (leRow : Row → Row → Prop) (rest : Ty Row) : Prop :=
  ∀ proper, IsRecord proper → ¬ Equivalent leRow rest proper

theorem opaque_record_no_view (label : Nat) (value : Ty Row) {rest : Ty Row}
    (notRigid : OpaqueTail leRow rest) :
    ¬ ∃ fields, View leRow (.record label value rest) fields := by
  rintro ⟨fields, view⟩
  cases view with
  | field same => exact notRigid _ (RigidRecordViews.spine_record _) same

theorem opaque_record (label : Nat) (value : Ty Row) {rest : Ty Row}
    (notRigid : OpaqueTail leRow rest) : OpaqueTail leRow (.record label value rest) := by
  intro proper rigid same
  have chain := (RigidRecordAtoms.atomic_iff_chain
    (RigidRecordAtoms.isRecord_atomic rigid) (by trivial)).mp same.2
  exact opaque_record_no_view label value notRigid
    (RigidRecordViews.Chain.view_forward chain (RigidRecordViews.record_has_view rigid))

/-- Covariance toward rigid tails cannot be used to reach an opaque demanded
record. Such a comparison is exactly the original head/tail congruence. -/
theorem opaque_comparison_iff (label : Nat) (left right source : Ty Row) {target : Ty Row}
    (notRigid : OpaqueTail leRow target) :
    Subtype leRow (.record label left source) (.record label right target) ↔
      Equivalent leRow left right ∧ Equivalent leRow source target := by
  constructor
  · intro below
    have chain := (RigidRecordAtoms.atomic_iff_chain (by trivial) (by trivial)).mp below
    have congruent := RigidRecordAtomNormal.Chain.opaque_target chain (by trivial)
      (opaque_record_no_view label right notRigid)
    cases congruent with
    | field head tail => exact ⟨head, tail⟩
  · rintro ⟨head, tail⟩
    exact (RigidSemanticRecords.record_congr label head tail).1

/-- For opaque tails the minimal relation can still distinguish payloads
which the outer field shadows. The criterion is exact, not just a counterexample. -/
theorem opaque_hidden_payload_iff (label : Nat) (visible first last : Ty Row)
    {rest : Ty Row} (notRigid : OpaqueTail leRow rest) :
    Subtype leRow (.record label visible (.record label first rest))
        (.record label visible (.record label last rest)) ↔
      Equivalent leRow first last := by
  constructor
  · intro below
    have tail := ((opaque_comparison_iff label visible visible _
      (opaque_record label last notRigid)).mp below).2
    exact ((opaque_comparison_iff label first last _ notRigid).mp tail.1).1
  · intro same
    exact (RigidSemanticRecords.record_congr label (.refl _)
      (RigidSemanticRecords.record_congr label same (.refl _))).1

theorem opaque_hidden_int_not_str (label : Nat) (visible : Ty Row) {rest : Ty Row}
    (notRigid : OpaqueTail leRow rest) :
    ¬ Subtype leRow (.record label visible (.record label (.base .int) rest))
      (.record label visible (.record label (.base .str) rest)) := by
  intro below
  exact RigidSemanticRecords.int_not_str
    ((opaque_hidden_payload_iff label visible (.base .int) (.base .str) notRigid).mp below).1

theorem admissible_records (label : Nat) (visible hidden : Ty Row) {rest : Ty Row}
    (admissible : Subtype leRow rest .emptyRecord) :
    Subtype leRow (.record label visible rest) .emptyRecord ∧
      Subtype leRow (.record label visible (.record label hidden rest)) .emptyRecord :=
  ⟨RigidSemanticRecords.record_width label visible admissible,
    RigidSemanticRecords.record_width label visible
      (RigidSemanticRecords.record_width label hidden admissible)⟩

/-- The two outer records are incomparable whenever inserting the hidden
field changes the opaque tail's equivalence class. -/
theorem hidden_insertion_incomparable (label : Nat) (visible hidden : Ty Row)
    {rest : Ty Row} (notRigid : OpaqueTail leRow rest)
    (changed : ¬ Equivalent leRow (.record label hidden rest) rest) :
    ¬ Subtype leRow (.record label visible (.record label hidden rest))
        (.record label visible rest) ∧
      ¬ Subtype leRow (.record label visible rest)
        (.record label visible (.record label hidden rest)) := by
  constructor
  · intro below
    exact changed ((opaque_comparison_iff label visible visible _ notRigid).mp below).2
  · intro below
    exact changed (((opaque_comparison_iff label visible visible _
      (opaque_record label hidden notRigid)).mp below).2.symm)

/-! ## The smallest admissible opaque tail -/

theorem never_opaque : OpaqueTail leRow (.bottom : Ty Row) := by
  intro proper rigid same
  exact RigidRecordAtoms.atomic_not_bottom (RigidRecordAtoms.isRecord_atomic rigid) same.2

theorem never_hidden_incomparable (label : Nat) (visible hidden : Ty Row) :
    ¬ Subtype leRow (.record label visible (.record label hidden .bottom))
        (.record label visible .bottom) ∧
      ¬ Subtype leRow (.record label visible .bottom)
        (.record label visible (.record label hidden .bottom)) :=
  hidden_insertion_incomparable label visible hidden never_opaque
    (fun same => RigidRecordAtoms.atomic_not_bottom (by trivial) same.1)

theorem never_both_admissible (label : Nat) (visible hidden : Ty Row) :
    Subtype leRow (.record label visible .bottom) .emptyRecord ∧
      Subtype leRow (.record label visible (.record label hidden .bottom)) .emptyRecord :=
  admissible_records label visible hidden (.bottom _)

/-! ## A union of two ordinary finite records -/

def yField : Ty Row := .record 1 (.base .int) .emptyRecord
def zField : Ty Row := .record 2 (.base .str) .emptyRecord
def unionTail : Ty Row := .union yField zField

theorem y_not_z : ¬ Subtype leRow (yField : Ty Row) zField := by
  intro below
  have impossible := RigidRecordFields.missing_mono below 2
    (by simp [RigidRecordFields.missing, yField])
  simp [RigidRecordFields.missing, zField] at impossible

theorem z_not_y : ¬ Subtype leRow (zField : Ty Row) yField := by
  intro below
  have impossible := RigidRecordFields.missing_mono below 1
    (by simp [RigidRecordFields.missing, zField])
  simp [RigidRecordFields.missing, yField] at impossible

theorem union_tail_admissible : Subtype leRow (unionTail : Ty Row) .emptyRecord :=
  .unionElim (RigidSemanticRecords.old_subtype (StructuralBase.record_width_to_empty (.field .empty)))
    (RigidSemanticRecords.old_subtype (StructuralBase.record_width_to_empty (.field .empty)))

/-- The demanded union cannot be represented by a proper record up to the
new relation; this is proved in the full declarative relation, not by syntax. -/
theorem union_tail_opaque : OpaqueTail leRow (unionTail : Ty Row) := by
  intro proper rigid same
  rcases RigidRecordAtoms.atomic_below_union (RigidRecordAtoms.isRecord_atomic rigid) same.2 with
    toY | toZ
  · exact z_not_y (.trans (.unionRight _ _) (.trans same.1 toY))
  · exact y_not_z (.trans (.unionLeft _ _) (.trans same.1 toZ))

theorem union_tail_missing_x : RigidRecordFields.missing 0 (unionTail : Ty Row) := by
  simp [RigidRecordFields.missing, unionTail, yField, zField]

theorem union_tail_changed (hidden : Ty Row) :
    ¬ Equivalent leRow (.record 0 hidden unionTail) unionTail := by
  intro same
  have impossible := RigidRecordFields.missing_mono same.2 0 union_tail_missing_x
  exact impossible.1 rfl

theorem union_hidden_incomparable (visible hidden : Ty Row) :
    ¬ Subtype leRow (.record 0 visible (.record 0 hidden unionTail))
        (.record 0 visible unionTail) ∧
      ¬ Subtype leRow (.record 0 visible unionTail)
        (.record 0 visible (.record 0 hidden unionTail)) :=
  hidden_insertion_incomparable 0 visible hidden union_tail_opaque (union_tail_changed hidden)

theorem union_both_admissible (visible hidden : Ty Row) :
    Subtype leRow (.record 0 visible unionTail) .emptyRecord ∧
      Subtype leRow (.record 0 visible (.record 0 hidden unionTail)) .emptyRecord :=
  admissible_records 0 visible hidden union_tail_admissible

theorem union_hidden_int_not_str (visible : Ty Row) :
    ¬ Subtype leRow (.record 0 visible (.record 0 (.base .int) unionTail))
      (.record 0 visible (.record 0 (.base .str) unionTail)) :=
  opaque_hidden_int_not_str 0 visible union_tail_opaque

end Yulang.RigidRecordOpaqueBoundary
