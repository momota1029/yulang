import Yulang.CommonNominalOptionalInspection
import Yulang.CommonNominalPlainInspection

/-!
# Fixed symbolic inspection into ordinary bound references

The bound syntax names original shared nodes and the finite auxiliary
constructors needed for required and optional fields. Its meaning is direct
common syntax, independent of any solution, projection table, or solver.

Inspection sees one known source constructor and emits finite alternative
lists of ordinary child comparisons. It never emits a dynamic Boolean or
profile atom. The optional target is precisely the dedicated union of exact
empty and a required field, not an arbitrary target union.

The local record-width hypotheses for optional inspection are explicit;
they are later supplied by the generated width constraints. These local
rules do not assert closure or termination of a repeated worklist.
-/

namespace Yulang.CommonNominalBoundInspection

open CommonNominalCarrier (Ty Row Subtype Equivalent)
open CommonNominalPlainInspection (Check)
open CommonNominalPayloadProjection (Payload)


inductive BoundRef (Node : Type) where
  | original : Node → BoundRef Node
  | top | width | exactEmpty
  | required : Nat → Option Node → BoundRef Node
  | optional : Nat → Option Node → BoundRef Node
  deriving DecidableEq

def payloadValue (values : Node → Ty) : Option Node → Ty
  | none => .top
  | some node => values node

def BoundRef.eval (values : Node → Ty) : BoundRef Node → Ty
  | .original node => values node
  | .top => .top
  | .width => CommonNominalCarrier.emptyRecord
  | .exactEmpty => CommonNominalCarrier.exactEmpty
  | .required label payload => CommonNominalCarrier.required label (payloadValue values payload)
  | .optional label payload =>
      .union CommonNominalCarrier.exactEmpty (CommonNominalCarrier.required label (payloadValue values payload))

def payloadRef : Option Node → BoundRef Node
  | none => .top
  | some node => .original node

@[simp] theorem payloadRef_eval (values : Node → Ty) (payload : Option Node) :
    (payloadRef payload).eval values = payloadValue values payload := by
  cases payload <;> rfl

abbrev Rigid (Rows : Type) (Node : Type) :=
  CommonNominalRigidInspection.Node Rows (BoundRef Node)

/-- One source layer. Every child is an explicitly shared bound reference. -/
inductive Source (Rows : Type) (Node : Type) where
  | reference : BoundRef Node → Source Rows Node
  | union : BoundRef Node → BoundRef Node → Source Rows Node
  | rigid : Rigid Rows Node → Source Rows Node
  | width | exactEmpty
  | record : Nat → BoundRef Node → BoundRef Node → Source Rows Node
  | recordDefault : Nat → BoundRef Node → BoundRef Node → Source Rows Node

def Source.eval (rows : Rows → Row) (values : Node → Ty) : Source Rows Node → Ty
  | .reference node => node.eval values
  | .union first last => .union (first.eval values) (last.eval values)
  | .rigid node => node.eval rows (BoundRef.eval values)
  | .width => CommonNominalCarrier.emptyRecord
  | .exactEmpty => CommonNominalCarrier.exactEmpty
  | .record label payload tail => CommonNominalCarrier.record label (payload.eval values) (tail.eval values)
  | .recordDefault label source fallback =>
      CommonNominalCarrier.recordDefault label (source.eval values) (fallback.eval values)

abbrev Output (Rows : Type) (Node : Type) := List (List (Check Rows (BoundRef Node)))

def Holds (rows : Rows → Row) (values : Node → Ty) (output : Output Rows Node) : Prop :=
  ∃ branch ∈ output, ∀ check ∈ branch, check.Holds rows (BoundRef.eval values)

def edge (source target : BoundRef Node) : Check Rows (BoundRef Node) :=
  .type source target

def defaultBranches (label : Nat) (source fallback : BoundRef Node) (payload : Option Node) :
    Output Rows Node :=
  [[edge .top (payloadRef payload), edge source .width],
    [edge source (.optional label payload), edge source (.required label none)],
    [edge source (.optional label payload), edge fallback (payloadRef payload)]]

/-- Required inspection needs no assumption about the source child's shape. -/
def inspectRequired (source : Source Rows Node) (label : Nat) (payload : Option Node) :
    Output Rows Node :=
  match source with
  | .reference node => [[edge node (.required label payload)]]
  | .union first last => [[edge first (.required label payload), edge last (.required label payload)]]
  | .rigid .bottom => [[]]
  | .record current head tail =>
      if label = current then [[edge head (payloadRef payload)]]
      else [[edge tail (.required label payload)]]
  | .recordDefault current base fallback =>
      if label = current then defaultBranches label base fallback payload
      else [[edge base (.required label payload)]]
  | _ => []

/-- The optional target has a dedicated fixed head, with no arbitrary union
or instantiation-dependent test used to decide its branches. -/
def inspectOptional (source : Source Rows Node) (label : Nat) (payload : Option Node) :
    Output Rows Node :=
  match source with
  | .reference node => [[edge node (.optional label payload)]]
  | .union first last => [[edge first (.optional label payload), edge last (.optional label payload)]]
  | .rigid .bottom | .exactEmpty => [[]]
  | .record current head tail =>
      if label = current then [[edge head (payloadRef payload)]]
      else [[edge tail (.optional label payload)]]
  | .recordDefault current base fallback =>
      if label = current then defaultBranches label base fallback payload
      else [[edge base (.optional label payload)]]
  | _ => []

def inspectWidth (source : Source Rows Node) : Output Rows Node :=
  match source with
  | .reference node => [[edge node .width]]
  | .union first last => [[edge first .width, edge last .width]]
  | .rigid .bottom | .width | .exactEmpty | .record _ _ _ | .recordDefault _ _ _ => [[]]
  | _ => []

/-- This is a premise on the original assignment, not a returned dynamic
guard. No width premise is imposed on a guarded payload or arrow argument. -/
def LocalWidth (values : Node → Ty) : Source Rows Node → Prop
  | .record _ _ tail => Subtype (tail.eval values) CommonNominalCarrier.emptyRecord
  | .recordDefault _ source _ => Subtype (source.eval values) CommonNominalCarrier.emptyRecord
  | _ => True

@[simp] theorem holds_empty (rows : Rows → Row) (values : Node → Ty) :
    ¬ Holds rows values ([] : Output Rows Node) := by
  simp [Holds]

@[simp] theorem holds_success (rows : Rows → Row) (values : Node → Ty) :
    Holds rows values ([[]] : Output Rows Node) := by
  simp [Holds]

@[simp] theorem holds_edge (rows : Rows → Row) (values : Node → Ty)
    (source target : BoundRef Node) :
    Holds rows values [[edge source target]] ↔ Subtype (source.eval values) (target.eval values) := by
  simp [Holds, edge, Check.Holds]

@[simp] theorem holds_two (rows : Rows → Row) (values : Node → Ty)
    (source target source' target' : BoundRef Node) :
    Holds rows values [[edge source target, edge source' target']] ↔
      Subtype (source.eval values) (target.eval values) ∧
        Subtype (source'.eval values) (target'.eval values) := by
  simp [Holds, edge, Check.Holds]

theorem default_branches_exact (rows : Rows → Row) (values : Node → Ty) (label : Nat)
    (source fallback : BoundRef Node) (payload : Option Node) :
    Holds rows values (defaultBranches label source fallback payload) ↔
      Subtype (CommonNominalCarrier.recordDefault label (source.eval values) (fallback.eval values))
        (CommonNominalCarrier.required label (payloadValue values payload)) := by
  rw [CommonNominalDefaultBounds.default_required_branches_exact]
  cases payload <;> simp [Holds, defaultBranches, 
    edge, Check.Holds, 
    BoundRef.eval, payloadRef, payloadValue, CommonNominalOptionalBound.guardedOptional]

theorem record_required_other (current label : Nat) (head tail payload : Ty)
    (different : label ≠ current) :
    Subtype (CommonNominalCarrier.record current head tail) (CommonNominalCarrier.required label payload) ↔
      Subtype tail (CommonNominalCarrier.required label payload) := by
  simp only [CommonNominalRecordTargetProfiles.subtype_required_iff]
  simp [CommonNominalPayloadProjection.fieldType, CommonNominalPayloadProjection.fieldProject,
    CommonNominalCarrier.record, different]

theorem default_required_other (current label : Nat) (source fallback payload : Ty)
    (different : label ≠ current) :
    Subtype (CommonNominalCarrier.recordDefault current source fallback) (CommonNominalCarrier.required label payload) ↔
      Subtype source (CommonNominalCarrier.required label payload) := by
  simp only [CommonNominalRecordTargetProfiles.subtype_required_iff]
  simp [CommonNominalPayloadProjection.fieldType, CommonNominalPayloadProjection.fieldProject,
    CommonNominalCarrier.recordDefault, different]

private theorem no_field_not_required (source payload : Ty) (label : Nat)
    (noField : CommonNominalPayloadProjection.fieldType [] label source = none) :
    ¬ Subtype source (CommonNominalCarrier.required label payload) := by
  rw [CommonNominalRecordTargetProfiles.subtype_required_iff, noField]
  exact id

theorem inspect_required_exact (rows : Rows → Row) (values : Node → Ty)
    (source : Source Rows Node) (label : Nat) (payload : Option Node) :
    Holds rows values (inspectRequired source label payload) ↔
      Subtype (source.eval rows values) ((BoundRef.required label payload).eval values) := by
  cases source with
  | reference node => exact holds_edge rows values node (.required label payload)
  | union first last =>
      simpa only [inspectRequired, holds_two, Source.eval, BoundRef.eval] using
        (CommonNominalCarrier.common_union_is_join (first.eval values) (last.eval values)
          (CommonNominalCarrier.required label (payloadValue values payload))).symm
  | record current head tail =>
      by_cases same : label = current
      · subst current
        simp only [inspectRequired, ↓reduceIte, holds_edge, payloadRef_eval, Source.eval]
        exact (CommonNominalCarrier.common_singleton_requirement_iff label _ _ _).symm
      · simp only [inspectRequired, same, ↓reduceIte, holds_edge, Source.eval, BoundRef.eval]
        exact (record_required_other current label _ _ _ same).symm
  | recordDefault current base fallback =>
      by_cases same : label = current
      · subst current
        simpa only [inspectRequired, ↓reduceIte, Source.eval, BoundRef.eval] using
          default_branches_exact rows values label base fallback payload
      · simp only [inspectRequired, same, ↓reduceIte, holds_edge, Source.eval, BoundRef.eval]
        exact (default_required_other current label _ _ _ same).symm
  | width | exactEmpty =>
      simp only [inspectRequired, holds_empty, Source.eval, BoundRef.eval, false_iff]
      exact no_field_not_required _ _ _ rfl
  | rigid node =>
      cases node with
      | bottom =>
          simp only [inspectRequired, holds_success, Source.eval,
            CommonNominalRigidInspection.Node.eval, true_iff]
          exact CommonNominalTypeFlow.bottom_below _
      | top | base | float | pair | variant | arrow | nominal =>
          simp only [inspectRequired, holds_empty, Source.eval,
            CommonNominalRigidInspection.Node.eval, BoundRef.eval, false_iff]
          exact no_field_not_required _ _ _ rfl

/-- Every child assignment is arbitrary; the only additional hypotheses
are the stated same-depth record-tail/default-source width inequalities. -/
theorem inspect_optional_exact (rows : Rows → Row) (values : Node → Ty)
    (source : Source Rows Node) (label : Nat) (payload : Option Node)
    (width : LocalWidth values source) :
    Holds rows values (inspectOptional source label payload) ↔
      Subtype (source.eval rows values) ((BoundRef.optional label payload).eval values) := by
  cases source with
  | reference node => exact holds_edge rows values node (.optional label payload)
  | union first last =>
      simpa only [inspectOptional, holds_two, Source.eval, BoundRef.eval,
        CommonNominalOptionalBound.guardedOptional] using
        (CommonNominalCarrier.common_union_is_join (first.eval values) (last.eval values)
          (CommonNominalOptionalBound.guardedOptional label (payloadValue values payload))).symm
  | record current head tail =>
      by_cases same : label = current
      · subst current
        simp only [inspectOptional, ↓reduceIte, holds_edge, payloadRef_eval, Source.eval]
        exact (CommonNominalOptionalInspection.record_same_iff label _ _ _).symm
      · simp only [inspectOptional, same, ↓reduceIte, holds_edge, Source.eval, BoundRef.eval]
        exact (CommonNominalOptionalInspection.record_other_iff current label _ _ _ same width).symm
  | recordDefault current base fallback =>
      by_cases same : label = current
      · subst current
        simp only [inspectOptional, ↓reduceIte, Source.eval, BoundRef.eval]
        exact (default_branches_exact rows values label base fallback payload).trans
          (CommonNominalOptionalInspection.default_same_iff label _ _ _ width).symm
      · simp only [inspectOptional, same, ↓reduceIte, holds_edge, Source.eval, BoundRef.eval]
        exact (CommonNominalOptionalInspection.default_other_iff current label _ _ _ same width).symm
  | width =>
      simp only [inspectOptional, holds_empty, Source.eval, BoundRef.eval, false_iff]
      exact CommonNominalOptionalInspection.width_not_below _ _
  | exactEmpty =>
      simp only [inspectOptional, holds_success, Source.eval, BoundRef.eval, true_iff]
      exact CommonNominalOptionalInspection.exactEmpty_below _ _
  | rigid node =>
      cases node with
      | bottom =>
          simp only [inspectOptional, holds_success, Source.eval,
            CommonNominalRigidInspection.Node.eval, true_iff]
          exact CommonNominalTypeFlow.bottom_below _
      | top =>
          simp only [inspectOptional, holds_empty, Source.eval,
            CommonNominalRigidInspection.Node.eval, BoundRef.eval, false_iff]
          exact CommonNominalOptionalInspection.top_not_below _ _
      | base scalar =>
          simp only [inspectOptional, holds_empty, Source.eval,
            CommonNominalRigidInspection.Node.eval, BoundRef.eval, false_iff]
          exact CommonNominalOptionalInspection.base_not_below _ _ _
      | float =>
          simp only [inspectOptional, holds_empty, Source.eval,
            CommonNominalRigidInspection.Node.eval, BoundRef.eval, false_iff]
          exact CommonNominalOptionalInspection.float_not_below _ _
      | nominal name arguments =>
          simp only [inspectOptional, holds_empty, Source.eval,
            CommonNominalRigidInspection.Node.eval, BoundRef.eval, false_iff]
          exact CommonNominalOptionalInspection.nominal_not_below _ _ _ _
      | pair first last =>
          simp only [inspectOptional, holds_empty, Source.eval,
            CommonNominalRigidInspection.Node.eval, BoundRef.eval, false_iff]
          exact CommonNominalOptionalInspection.pair_not_below _ _ _ _
      | variant tag child =>
          simp only [inspectOptional, holds_empty, Source.eval,
            CommonNominalRigidInspection.Node.eval, BoundRef.eval, false_iff]
          exact CommonNominalOptionalInspection.variant_not_below _ _ _ _
      | arrow input incoming output outgoing =>
          simp only [inspectOptional, holds_empty, Source.eval,
            CommonNominalRigidInspection.Node.eval, BoundRef.eval, false_iff]
          exact CommonNominalOptionalInspection.arrow_not_below _ _ _ _ _ _

theorem inspect_width_exact (rows : Rows → Row) (values : Node → Ty)
    (source : Source Rows Node) :
    Holds rows values (inspectWidth source) ↔
      Subtype (source.eval rows values) CommonNominalCarrier.emptyRecord := by
  cases source with
  | reference node => exact holds_edge rows values node .width
  | union first last =>
      simpa only [inspectWidth, holds_two, Source.eval, BoundRef.eval] using
        (CommonNominalCarrier.common_union_is_join (first.eval values) (last.eval values) CommonNominalCarrier.emptyRecord).symm
  | record | recordDefault | width | exactEmpty =>
      simp [inspectWidth, Source.eval, CommonNominalRecordTargetProfiles.subtype_emptyRecord_iff,
        CommonNominalCarrier.record, CommonNominalCarrier.recordDefault, CommonNominalCarrier.exactEmpty,
        CommonNominalDefaultRequired.recordShape] <;> rfl
  | rigid node =>
      cases node <;>
        simp [inspectWidth, Source.eval, CommonNominalRigidInspection.Node.eval,
          CommonNominalRecordTargetProfiles.subtype_emptyRecord_iff, CommonNominalDefaultRequired.recordShape,
          CommonNominalCarrier.pair, CommonNominalCarrier.variant, CommonNominalCarrier.arrow, CommonNominalCarrier.nominal]

end Yulang.CommonNominalBoundInspection
