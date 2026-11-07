import Yulang.CommonOptionalInspection
import Yulang.CommonSymbolicRigidInspection

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

namespace Yulang.CommonSymbolicBoundInspection

open Common (Ty Row Subtype Equivalent)
open CommonSymbolicConstraints (Check Branch Alternatives)
open CommonPayloadProjection (Payload)

universe u v

inductive BoundRef (Node : Type v) where
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
  | .width => Common.emptyRecord
  | .exactEmpty => Common.exactEmpty
  | .required label payload => Common.required label (payloadValue values payload)
  | .optional label payload =>
      .union Common.exactEmpty (Common.required label (payloadValue values payload))

def payloadRef : Option Node → BoundRef Node
  | none => .top
  | some node => .original node

@[simp] theorem payloadRef_eval (values : Node → Ty) (payload : Option Node) :
    (payloadRef payload).eval values = payloadValue values payload := by
  cases payload <;> rfl

abbrev Rigid (Rows : Type u) (Node : Type v) :=
  CommonSymbolicRigidInspection.Node Rows (BoundRef Node)

/-- One source layer. Every child is an explicitly shared bound reference. -/
inductive Source (Rows : Type u) (Node : Type v) where
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
  | .width => Common.emptyRecord
  | .exactEmpty => Common.exactEmpty
  | .record label payload tail => Common.record label (payload.eval values) (tail.eval values)
  | .recordDefault label source fallback =>
      Common.recordDefault label (source.eval values) (fallback.eval values)

abbrev Output (Rows : Type u) (Node : Type v) := Alternatives Rows Node (BoundRef Node)

def Holds (rows : Rows → Row) (values : Node → Ty) (output : Output Rows Node) : Prop :=
  Alternatives.Holds rows values (BoundRef.eval values) output

def edge (source target : BoundRef Node) : Check Rows Node (BoundRef Node) :=
  .childBelow (.ref source) (.ref target)

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
  | .record _ _ tail => Subtype (tail.eval values) Common.emptyRecord
  | .recordDefault _ source _ => Subtype (source.eval values) Common.emptyRecord
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
  simp [Holds, edge, CommonSymbolicConstraints.Branch.Holds, Check.Holds, Payload.evalLayer]

@[simp] theorem holds_two (rows : Rows → Row) (values : Node → Ty)
    (source target source' target' : BoundRef Node) :
    Holds rows values [[edge source target, edge source' target']] ↔
      Subtype (source.eval values) (target.eval values) ∧
        Subtype (source'.eval values) (target'.eval values) := by
  simp [Holds, edge, CommonSymbolicConstraints.Branch.Holds, Check.Holds, Payload.evalLayer]

theorem default_branches_exact (rows : Rows → Row) (values : Node → Ty) (label : Nat)
    (source fallback : BoundRef Node) (payload : Option Node) :
    Holds rows values (defaultBranches label source fallback payload) ↔
      Subtype (Common.recordDefault label (source.eval values) (fallback.eval values))
        (Common.required label (payloadValue values payload)) := by
  rw [CommonDefaultBounds.default_required_branches_exact]
  cases payload <;> simp [Holds, defaultBranches, CommonSymbolicConstraints.Alternatives.Holds,
    CommonSymbolicConstraints.Branch.Holds, edge, Check.Holds, Payload.evalLayer,
    BoundRef.eval, payloadRef, payloadValue, CommonOptionalBound.guardedOptional]

theorem record_required_other (current label : Nat) (head tail payload : Ty)
    (different : label ≠ current) :
    Subtype (Common.record current head tail) (Common.required label payload) ↔
      Subtype tail (Common.required label payload) := by
  simp only [CommonRecordTargetProfiles.subtype_required_iff]
  simp [CommonPayloadProjection.fieldType, CommonPayloadProjection.fieldProject,
    Common.record, different]

theorem default_required_other (current label : Nat) (source fallback payload : Ty)
    (different : label ≠ current) :
    Subtype (Common.recordDefault current source fallback) (Common.required label payload) ↔
      Subtype source (Common.required label payload) := by
  simp only [CommonRecordTargetProfiles.subtype_required_iff]
  simp [CommonPayloadProjection.fieldType, CommonPayloadProjection.fieldProject,
    Common.recordDefault, different]

private theorem no_field_not_required (source payload : Ty) (label : Nat)
    (noField : CommonPayloadProjection.fieldType [] label source = none) :
    ¬ Subtype source (Common.required label payload) := by
  rw [CommonRecordTargetProfiles.subtype_required_iff, noField]
  exact id

theorem inspect_required_exact (rows : Rows → Row) (values : Node → Ty)
    (source : Source Rows Node) (label : Nat) (payload : Option Node) :
    Holds rows values (inspectRequired source label payload) ↔
      Subtype (source.eval rows values) ((BoundRef.required label payload).eval values) := by
  cases source with
  | reference node => exact holds_edge rows values node (.required label payload)
  | union first last =>
      simpa only [inspectRequired, holds_two, Source.eval, BoundRef.eval] using
        (Common.common_union_is_join (first.eval values) (last.eval values)
          (Common.required label (payloadValue values payload))).symm
  | record current head tail =>
      by_cases same : label = current
      · subst current
        simp only [inspectRequired, ↓reduceIte, holds_edge, payloadRef_eval, Source.eval]
        exact (Common.common_singleton_requirement_iff label _ _ _).symm
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
            CommonSymbolicRigidInspection.Node.eval, true_iff]
          exact CommonBoundCoalescing.bottom_le _
      | top | base | pair | variant | arrow =>
          simp only [inspectRequired, holds_empty, Source.eval,
            CommonSymbolicRigidInspection.Node.eval, BoundRef.eval, false_iff]
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
        CommonOptionalBound.guardedOptional] using
        (Common.common_union_is_join (first.eval values) (last.eval values)
          (CommonOptionalBound.guardedOptional label (payloadValue values payload))).symm
  | record current head tail =>
      by_cases same : label = current
      · subst current
        simp only [inspectOptional, ↓reduceIte, holds_edge, payloadRef_eval, Source.eval]
        exact (CommonOptionalInspection.record_same_iff label _ _ _).symm
      · simp only [inspectOptional, same, ↓reduceIte, holds_edge, Source.eval, BoundRef.eval]
        exact (CommonOptionalInspection.record_other_iff current label _ _ _ same width).symm
  | recordDefault current base fallback =>
      by_cases same : label = current
      · subst current
        simp only [inspectOptional, ↓reduceIte, Source.eval, BoundRef.eval]
        exact (default_branches_exact rows values label base fallback payload).trans
          (CommonOptionalInspection.default_same_iff label _ _ _ width).symm
      · simp only [inspectOptional, same, ↓reduceIte, holds_edge, Source.eval, BoundRef.eval]
        exact (CommonOptionalInspection.default_other_iff current label _ _ _ same width).symm
  | width =>
      simp only [inspectOptional, holds_empty, Source.eval, BoundRef.eval, false_iff]
      exact CommonOptionalInspection.width_not_below _ _
  | exactEmpty =>
      simp only [inspectOptional, holds_success, Source.eval, BoundRef.eval, true_iff]
      exact CommonOptionalInspection.exactEmpty_below _ _
  | rigid node =>
      cases node with
      | bottom =>
          simp only [inspectOptional, holds_success, Source.eval,
            CommonSymbolicRigidInspection.Node.eval, true_iff]
          exact CommonBoundCoalescing.bottom_le _
      | top =>
          simp only [inspectOptional, holds_empty, Source.eval,
            CommonSymbolicRigidInspection.Node.eval, BoundRef.eval, false_iff]
          exact CommonOptionalInspection.top_not_below _ _
      | base scalar =>
          simp only [inspectOptional, holds_empty, Source.eval,
            CommonSymbolicRigidInspection.Node.eval, BoundRef.eval, false_iff]
          exact CommonOptionalInspection.base_not_below _ _ _
      | pair first last =>
          simp only [inspectOptional, holds_empty, Source.eval,
            CommonSymbolicRigidInspection.Node.eval, BoundRef.eval, false_iff]
          exact CommonOptionalInspection.pair_not_below _ _ _ _
      | variant tag child =>
          simp only [inspectOptional, holds_empty, Source.eval,
            CommonSymbolicRigidInspection.Node.eval, BoundRef.eval, false_iff]
          exact CommonOptionalInspection.variant_not_below _ _ _ _
      | arrow input incoming output outgoing =>
          simp only [inspectOptional, holds_empty, Source.eval,
            CommonSymbolicRigidInspection.Node.eval, BoundRef.eval, false_iff]
          exact CommonOptionalInspection.arrow_not_below _ _ _ _ _ _

theorem inspect_width_exact (rows : Rows → Row) (values : Node → Ty)
    (source : Source Rows Node) :
    Holds rows values (inspectWidth source) ↔
      Subtype (source.eval rows values) Common.emptyRecord := by
  cases source with
  | reference node => exact holds_edge rows values node .width
  | union first last =>
      simpa only [inspectWidth, holds_two, Source.eval, BoundRef.eval] using
        (Common.common_union_is_join (first.eval values) (last.eval values) Common.emptyRecord).symm
  | record | recordDefault | width | exactEmpty =>
      simp [inspectWidth, Source.eval, CommonRecordTargetProfiles.subtype_emptyRecord_iff,
        Common.record, Common.recordDefault, Common.exactEmpty,
        CommonDefaultRequired.recordShape] <;> rfl
  | rigid node =>
      cases node <;>
        simp [inspectWidth, Source.eval, CommonSymbolicRigidInspection.Node.eval,
          CommonRecordTargetProfiles.subtype_emptyRecord_iff, CommonDefaultRequired.recordShape,
          Common.pair, Common.variant, Common.arrow]

/-- Syntactic output restriction: no profile, computed flag, or compound
payload expression is an atom of this inspector. -/
def PlainCheck : Check Rows Node (BoundRef Node) → Prop
  | .childBelow (.ref _) (.ref _) => True
  | .rowBelow _ _ => True
  | .flag (.literal _) => True
  | _ => False

def Plain (output : Output Rows Node) : Prop :=
  ∀ branch ∈ output, ∀ check ∈ branch, PlainCheck check

theorem default_branches_plain (label : Nat) (source fallback : BoundRef Node)
    (payload : Option Node) : Plain (Rows := Rows) (defaultBranches label source fallback payload) := by
  simp [Plain, defaultBranches, edge, PlainCheck]

theorem inspect_required_plain (source : Source Rows Node) (label : Nat) (payload : Option Node) :
    Plain (inspectRequired source label payload) := by
  cases source with
  | reference | union | width | exactEmpty => simp [inspectRequired, Plain, edge, PlainCheck]
  | record current head tail =>
      by_cases same : label = current <;>
        simp [inspectRequired, same, Plain, edge, PlainCheck]
  | recordDefault current base fallback =>
      by_cases same : label = current <;>
        simp [inspectRequired, same, Plain, defaultBranches, edge, PlainCheck]
  | rigid node => cases node <;> simp [inspectRequired, Plain, PlainCheck]

theorem inspect_optional_plain (source : Source Rows Node) (label : Nat) (payload : Option Node) :
    Plain (inspectOptional source label payload) := by
  cases source with
  | reference | union | width | exactEmpty => simp [inspectOptional, Plain, edge, PlainCheck]
  | record current head tail =>
      by_cases same : label = current <;>
        simp [inspectOptional, same, Plain, edge, PlainCheck]
  | recordDefault current base fallback =>
      by_cases same : label = current <;>
        simp [inspectOptional, same, Plain, defaultBranches, edge, PlainCheck]
  | rigid node => cases node <;> simp [inspectOptional, Plain, PlainCheck]

theorem inspect_width_plain (source : Source Rows Node) : Plain (inspectWidth source) := by
  cases source with
  | reference | union | record | recordDefault | width | exactEmpty =>
      simp [inspectWidth, Plain, edge, PlainCheck]
  | rigid node => cases node <;> simp [inspectWidth, Plain, PlainCheck]

end Yulang.CommonSymbolicBoundInspection
