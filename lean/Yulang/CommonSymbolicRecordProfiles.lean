import Yulang.CommonRecordTailProfiles
import Yulang.CommonRecordEnvelope

/-!
# Symbolic record profiles with shared unknown references

Compilation traverses finite syntax without reading row or type assignments.
An unknown same-depth node keeps its original identifier, query label and
outer mask. Proper payload children use the existing finite `Payload` syntax.
All constructor, union/intersection, presence and optional-profile branches
are therefore fixed before any parameter is chosen.

The independent interpretation below may read a projection primitive at an
arbitrary common node. Its exactness is not a solver-success certificate:
every row assignment and every regular type assignment is quantified. This
module does not replace arbitrary unknown tails by a fixed finite label table
and does not claim the complete saturation theorem.
-/

namespace Yulang.CommonSymbolicRecordProfiles

open Common (Ty Row)
open CommonPayloadProjection (Payload)

universe u v w

/-- These are observations of one original shared node, not freshly allocated
variables. In particular the mask is part of a field query's identity. -/
inductive GuardAtom (Node : Type u) where
  | records : Node → GuardAtom Node
  | outsideRecords : Node → GuardAtom Node
  | present : List Nat → Nat → Node → GuardAtom Node
  | initialField : List Nat → Nat → Node → GuardAtom Node
  | initialOptional : List Nat → Nat → Node → GuardAtom Node

inductive BoolExpr (Node : Type u) where
  | literal : Bool → BoolExpr Node
  | atom : GuardAtom Node → BoolExpr Node
  | and : BoolExpr Node → BoolExpr Node → BoolExpr Node
  | or : BoolExpr Node → BoolExpr Node → BoolExpr Node
  | not : BoolExpr Node → BoolExpr Node

def GuardAtom.eval (nodes : Node → Ty) : GuardAtom Node → Bool
  | .records node => CommonDefaultRequired.recordShape (nodes node)
  | .outsideRecords node => CommonRecordEnvelope.outsideRecords (nodes node)
  | .present hidden label node => CommonDefaultRequired.fieldPresence hidden label (nodes node)
  | .initialField hidden label node => CommonRecordTailProfiles.initialField hidden label (nodes node)
  | .initialOptional hidden label node => CommonRecordTailProfiles.initialOptional hidden label (nodes node)

def BoolExpr.eval (nodes : Node → Ty) : BoolExpr Node → Bool
  | .literal value => value
  | .atom query => query.eval nodes
  | .and first last => first.eval nodes && last.eval nodes
  | .or first last => first.eval nodes || last.eval nodes
  | .not value => !value.eval nodes

inductive ProjectionKind where
  | field | optional
  deriving DecidableEq, Repr

def ProjectionKind.eval (kind : ProjectionKind) (hidden : List Nat) (label : Nat)
    (source : Ty) : Option Ty :=
  match kind with
  | .field => CommonPayloadProjection.fieldType hidden label source
  | .optional => CommonPayloadProjection.optionalType hidden label source

def bothTypes : Option Ty → Option Ty → Option Ty
  | some first, some last => some (.union first last)
  | _, _ => none

def eitherTypes : Option Ty → Option Ty → Option Ty
  | none, last => last
  | first, none => first
  | some first, some last => some (.inter first last)

def withTrivialType : Option Ty → Option Ty
  | none => some .top
  | some payload => some payload

/-- `none` and `some top` are distinct. The former does not even accept the
trivial payload observation. Boolean choices are retained as finite syntax. -/
inductive ProfileExpr (Node : Type u) (Child : Type v) where
  | none : ProfileExpr Node Child
  | some : Payload Child → ProfileExpr Node Child
  | project : ProjectionKind → List Nat → Nat → Node → ProfileExpr Node Child
  | both : ProfileExpr Node Child → ProfileExpr Node Child → ProfileExpr Node Child
  | either : ProfileExpr Node Child → ProfileExpr Node Child → ProfileExpr Node Child
  | withTrivial : ProfileExpr Node Child → ProfileExpr Node Child
  | ite : BoolExpr Node → ProfileExpr Node Child → ProfileExpr Node Child → ProfileExpr Node Child

def ProfileExpr.eval (nodes : Node → Ty) (children : Child → Ty) : ProfileExpr Node Child → Option Ty
  | .none => Option.none
  | .some payload => Option.some (payload.evalLayer children)
  | .project kind hidden label node => kind.eval hidden label (nodes node)
  | .both first last => bothTypes (first.eval nodes children) (last.eval nodes children)
  | .either first last => eitherTypes (first.eval nodes children) (last.eval nodes children)
  | .withTrivial profile => withTrivialType (profile.eval nodes children)
  | .ite condition yes no => if condition.eval nodes then yes.eval nodes children else no.eval nodes children

/-- A finite outer layer with distinct same-depth references and guarded
payload references. The row syntax is left uninterpreted by the compiler. -/
inductive OpenLayer (Rows : Type u) (Node : Type v) (Child : Type w) where
  | ref : Node → OpenLayer Rows Node Child
  | base : Inference.Base → OpenLayer Rows Node Child
  | bottom : OpenLayer Rows Node Child
  | top : OpenLayer Rows Node Child
  | union : OpenLayer Rows Node Child → OpenLayer Rows Node Child → OpenLayer Rows Node Child
  | inter : OpenLayer Rows Node Child → OpenLayer Rows Node Child → OpenLayer Rows Node Child
  | pair : Child → Child → OpenLayer Rows Node Child
  | emptyRecord : OpenLayer Rows Node Child
  | exactEmpty : OpenLayer Rows Node Child
  | record : Nat → Child → OpenLayer Rows Node Child → OpenLayer Rows Node Child
  | recordDefault : Nat → OpenLayer Rows Node Child → Child → OpenLayer Rows Node Child
  | variant : Nat → Child → OpenLayer Rows Node Child
  | arrow : Child → Rows → Child → Rows → OpenLayer Rows Node Child
  | mask : List Nat → OpenLayer Rows Node Child → OpenLayer Rows Node Child

def OpenLayer.eval (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty) :
    OpenLayer Rows Node Child → Ty
  | .ref node => nodes node
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (first.eval rows nodes children) (last.eval rows nodes children)
  | .inter first last => .inter (first.eval rows nodes children) (last.eval rows nodes children)
  | .pair first last => Common.pair (children first) (children last)
  | .emptyRecord => Common.emptyRecord
  | .exactEmpty => Common.exactEmpty
  | .record label payload tail => Common.record label (children payload) (tail.eval rows nodes children)
  | .recordDefault label source fallback =>
      Common.recordDefault label (source.eval rows nodes children) (children fallback)
  | .variant label payload => Common.variant label (children payload)
  | .arrow input incoming output outgoing =>
      Common.arrow (children input) (rows incoming) (children output) (rows outgoing)
  | .mask hidden source => Common.mask hidden (source.eval rows nodes children)

structure Summary (Node : Type u) (Child : Type v) where
  records : BoolExpr Node
  outsideRecords : BoolExpr Node
  present : BoolExpr Node
  initialField : BoolExpr Node
  initialOptional : BoolExpr Node
  field : ProfileExpr Node Child
  optional : ProfileExpr Node Child

namespace Summary

def ref (hidden : List Nat) (label : Nat) (node : Node) : Summary Node Child :=
  ⟨.atom (.records node), .atom (.outsideRecords node), .atom (.present hidden label node),
    .atom (.initialField hidden label node), .atom (.initialOptional hidden label node),
    .project .field hidden label node, .project .optional hidden label node⟩

def scalar : Summary Node Child :=
  ⟨.literal false, .literal true, .literal false, .literal false, .literal false, .none, .none⟩

def bottom : Summary Node Child :=
  ⟨.literal true, .literal true, .literal true, .literal true, .literal true, .some .bottom, .some .bottom⟩

def top : Summary Node Child :=
  ⟨.literal false, .literal false, .literal false, .literal false, .literal false, .none, .none⟩

def emptyRecord : Summary Node Child :=
  ⟨.literal true, .literal false, .literal false, .literal false, .literal false, .none, .some .top⟩

def exactEmpty (hidden : List Nat) (label : Nat) : Summary Node Child :=
  ⟨.literal true, .literal false, .literal false, .literal false, .literal (decide (label ∉ hidden)),
    .none, if label ∈ hidden then .some .top else .some .bottom⟩

def union (first last : Summary Node Child) : Summary Node Child :=
  ⟨.and first.records last.records, .and first.outsideRecords last.outsideRecords,
    .and first.present last.present, .and first.initialField last.initialField,
    .and first.initialOptional last.initialOptional, .both first.field last.field, .both first.optional last.optional⟩

def inter (first last : Summary Node Child) : Summary Node Child :=
  ⟨.or first.records last.records, .or first.outsideRecords last.outsideRecords,
    .or first.present last.present, .or first.initialField last.initialField,
    .or first.initialOptional last.initialOptional, .either first.field last.field, .either first.optional last.optional⟩

def record (hidden : List Nat) (label current : Nat) (payload : Child)
    (tail : Summary Node Child) : Summary Node Child :=
  if label = current ∧ current ∉ hidden then
    ⟨.literal true, .literal false, .literal true, .literal true, .literal true,
      .some (.ref payload), .some (.ref payload)⟩
  else
    ⟨.literal true, .literal false, tail.present, tail.initialField, tail.initialOptional,
      tail.field, .withTrivial tail.optional⟩

def recordDefault (hidden : List Nat) (label current : Nat) (source : Summary Node Child)
    (fallback : Child) : Summary Node Child :=
  if label = current ∧ current ∉ hidden then
    let selected := ProfileExpr.both source.optional
      (.ite source.present (.some .bottom) (.some (.ref fallback)))
    ⟨.literal true, .literal false, source.records, .literal true, .literal true,
      selected, .withTrivial selected⟩
  else
    ⟨.literal true, .literal false, source.present, source.initialField, source.initialOptional,
      source.field, .withTrivial source.optional⟩

end Summary

/-- This total compiler has no row assignment, node assignment or success
argument. Even an unknown default source is compiled before substitution. -/
def compile (hidden : List Nat) (label : Nat) : OpenLayer Rows Node Child → Summary Node Child
  | .ref node => Summary.ref hidden label node
  | .bottom => Summary.bottom
  | .top => Summary.top
  | .union first last => Summary.union (compile hidden label first) (compile hidden label last)
  | .inter first last => Summary.inter (compile hidden label first) (compile hidden label last)
  | .emptyRecord => Summary.emptyRecord
  | .exactEmpty => Summary.exactEmpty hidden label
  | .record current payload tail => Summary.record hidden label current payload (compile hidden label tail)
  | .recordDefault current source fallback =>
      Summary.recordDefault hidden label current (compile hidden label source) fallback
  | .mask more source => compile (hidden ++ more) label source
  | _ => Summary.scalar

structure Meaning where
  records : Bool
  outsideRecords : Bool
  present : Bool
  initialField : Bool
  initialOptional : Bool
  field : Option Ty
  optional : Option Ty

def Summary.eval (nodes : Node → Ty) (children : Child → Ty) (summary : Summary Node Child) : Meaning :=
  ⟨summary.records.eval nodes, summary.outsideRecords.eval nodes, summary.present.eval nodes,
    summary.initialField.eval nodes, summary.initialOptional.eval nodes,
    summary.field.eval nodes children, summary.optional.eval nodes children⟩

def meaning (hidden : List Nat) (label : Nat) (source : Ty) : Meaning :=
  ⟨CommonDefaultRequired.recordShape source, CommonRecordEnvelope.outsideRecords source,
    CommonDefaultRequired.fieldPresence hidden label source,
    CommonRecordTailProfiles.initialField hidden label source,
    CommonRecordTailProfiles.initialOptional hidden label source,
    CommonPayloadProjection.fieldType hidden label source,
    CommonPayloadProjection.optionalType hidden label source⟩

private theorem map_both (first last : CommonPayloadProjection.Profile (CommonSyntax.State Row)) :
    (CommonPayloadProjection.Profile.both first last).map Payload.common =
      bothTypes (first.map Payload.common) (last.map Payload.common) := by
  cases first <;> cases last <;> rfl

private theorem map_either (first last : CommonPayloadProjection.Profile (CommonSyntax.State Row)) :
    (CommonPayloadProjection.Profile.either first last).map Payload.common =
      eitherTypes (first.map Payload.common) (last.map Payload.common) := by
  cases first <;> cases last <;> rfl

private theorem map_withTrivial (profile : CommonPayloadProjection.Profile (CommonSyntax.State Row)) :
    (CommonPayloadProjection.Profile.withTrivial profile).map Payload.common =
      withTrivialType (profile.map Payload.common) := by
  cases profile <;> rfl

private theorem field_union (hidden : List Nat) (label : Nat) (first last : Ty) :
    CommonPayloadProjection.fieldType hidden label (.union first last) =
      bothTypes (CommonPayloadProjection.fieldType hidden label first)
        (CommonPayloadProjection.fieldType hidden label last) := map_both _ _

private theorem optional_union (hidden : List Nat) (label : Nat) (first last : Ty) :
    CommonPayloadProjection.optionalType hidden label (.union first last) =
      bothTypes (CommonPayloadProjection.optionalType hidden label first)
        (CommonPayloadProjection.optionalType hidden label last) := map_both _ _

private theorem field_inter (hidden : List Nat) (label : Nat) (first last : Ty) :
    CommonPayloadProjection.fieldType hidden label (.inter first last) =
      eitherTypes (CommonPayloadProjection.fieldType hidden label first)
        (CommonPayloadProjection.fieldType hidden label last) := map_either _ _

private theorem optional_inter (hidden : List Nat) (label : Nat) (first last : Ty) :
    CommonPayloadProjection.optionalType hidden label (.inter first last) =
      eitherTypes (CommonPayloadProjection.optionalType hidden label first)
        (CommonPayloadProjection.optionalType hidden label last) := map_either _ _

private theorem field_record (hidden : List Nat) (label current : Nat) (payload tail : Ty) :
    CommonPayloadProjection.fieldType hidden label (Common.record current payload tail) =
      if label = current ∧ current ∉ hidden then some payload
      else CommonPayloadProjection.fieldType hidden label tail := by
  by_cases active : label = current ∧ current ∉ hidden <;>
    simp [CommonPayloadProjection.fieldType, CommonPayloadProjection.fieldProject, Common.record,
      active, Payload.common, Payload.evalLayer]

private theorem optional_record (hidden : List Nat) (label current : Nat) (payload tail : Ty) :
    CommonPayloadProjection.optionalType hidden label (Common.record current payload tail) =
      if label = current ∧ current ∉ hidden then some payload
      else withTrivialType (CommonPayloadProjection.optionalType hidden label tail) := by
  by_cases active : label = current ∧ current ∉ hidden <;>
    simp [CommonPayloadProjection.optionalType, CommonPayloadProjection.optionalProject, Common.record,
      active, Payload.common, Payload.evalLayer, map_withTrivial]

private theorem field_default (hidden : List Nat) (label current : Nat) (source fallback : Ty) :
    CommonPayloadProjection.fieldType hidden label (Common.recordDefault current source fallback) =
      if label = current ∧ current ∉ hidden then
        bothTypes (CommonPayloadProjection.optionalType hidden label source)
          (if CommonDefaultRequired.fieldPresence hidden label source then some .bottom else some fallback)
      else CommonPayloadProjection.fieldType hidden label source := by
  by_cases active : label = current ∧ current ∉ hidden
  · simp only [Common.recordDefault, CommonPayloadProjection.fieldType,
      CommonPayloadProjection.fieldProject, ite_eq_left active, map_both]
    cases CommonDefaultRequired.fieldPresence hidden label source <;> rfl
  · simp [Common.recordDefault, CommonPayloadProjection.fieldType,
      CommonPayloadProjection.fieldProject, active]

private theorem optional_default (hidden : List Nat) (label current : Nat) (source fallback : Ty) :
    CommonPayloadProjection.optionalType hidden label (Common.recordDefault current source fallback) =
      withTrivialType (if label = current ∧ current ∉ hidden then
        bothTypes (CommonPayloadProjection.optionalType hidden label source)
          (if CommonDefaultRequired.fieldPresence hidden label source then some .bottom else some fallback)
      else CommonPayloadProjection.optionalType hidden label source) := by
  by_cases active : label = current ∧ current ∉ hidden
  · simp only [Common.recordDefault, CommonPayloadProjection.optionalType,
      CommonPayloadProjection.optionalProject, ite_eq_left active, map_withTrivial, map_both]
    cases CommonDefaultRequired.fieldPresence hidden label source <;> rfl
  · simp [Common.recordDefault, CommonPayloadProjection.optionalType,
      CommonPayloadProjection.optionalProject, active, map_withTrivial]

/-- All seven inspections are exact simultaneously, for arbitrary independent
row, same-depth-node and guarded-child interpretations. No graph equations
or restrictions on regular children are premises. -/
theorem compile_exact (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty)
    (hidden : List Nat) (label : Nat) (source : OpenLayer Rows Node Child) :
    (compile hidden label source).eval nodes children = meaning hidden label (source.eval rows nodes children) := by
  induction source generalizing hidden with
  | ref node => rfl
  | base | bottom | top | pair | emptyRecord | variant | arrow => rfl
  | exactEmpty =>
      by_cases member : label ∈ hidden <;>
        simp [compile, Summary.exactEmpty, Summary.eval, BoolExpr.eval, ProfileExpr.eval,
          meaning, OpenLayer.eval, Common.exactEmpty, CommonDefaultRequired.recordShape,
          CommonRecordEnvelope.outsideRecords, CommonDefaultRequired.fieldPresence,
          CommonRecordTailProfiles.initialField, CommonRecordTailProfiles.initialOptional,
          CommonPayloadProjection.fieldType, CommonPayloadProjection.optionalType,
          CommonPayloadProjection.fieldProject, CommonPayloadProjection.optionalProject,
          member, Payload.evalLayer, Payload.common]
  | union first last before after | inter first last before after =>
      have left := before hidden
      have right := after hidden
      simp only [Summary.eval, meaning, Meaning.mk.injEq] at left right
      simp only [compile, Summary.union, Summary.inter, Summary.eval, BoolExpr.eval,
        ProfileExpr.eval, OpenLayer.eval, meaning, CommonDefaultRequired.recordShape,
        CommonRecordEnvelope.outsideRecords, CommonDefaultRequired.fieldPresence,
        CommonRecordTailProfiles.initialField, CommonRecordTailProfiles.initialOptional,
        field_union, optional_union, field_inter, optional_inter, Meaning.mk.injEq]
      exact ⟨by rw [left.1, right.1], by rw [left.2.1, right.2.1],
        by rw [left.2.2.1, right.2.2.1], by rw [left.2.2.2.1, right.2.2.2.1],
        by rw [left.2.2.2.2.1, right.2.2.2.2.1],
        by rw [left.2.2.2.2.2.1, right.2.2.2.2.2.1],
        by rw [left.2.2.2.2.2.2, right.2.2.2.2.2.2]⟩
  | record current payload tail ih =>
      have inner := ih hidden
      simp only [Summary.eval, meaning, Meaning.mk.injEq] at inner
      simp only [compile, Summary.eval, OpenLayer.eval, meaning, field_record, optional_record]
      by_cases active : label = current ∧ current ∉ hidden
      · simp only [Summary.record, ite_eq_left active, BoolExpr.eval, ProfileExpr.eval,
          Common.record, CommonDefaultRequired.recordShape,
          CommonRecordEnvelope.outsideRecords, CommonDefaultRequired.fieldPresence,
          CommonRecordTailProfiles.initialField, CommonRecordTailProfiles.initialOptional,
          Payload.evalLayer]
      · simp only [Summary.record, ite_eq_right active, BoolExpr.eval, ProfileExpr.eval,
          Common.record, CommonDefaultRequired.recordShape,
          CommonRecordEnvelope.outsideRecords, CommonDefaultRequired.fieldPresence,
          CommonRecordTailProfiles.initialField, CommonRecordTailProfiles.initialOptional]
        simp_all only
  | recordDefault current source fallback ih =>
      have inner := ih hidden
      simp only [Summary.eval, meaning, Meaning.mk.injEq] at inner
      simp only [compile, Summary.eval, OpenLayer.eval, meaning, field_default, optional_default]
      by_cases active : label = current ∧ current ∉ hidden
      · simp only [Summary.recordDefault, ite_eq_left active, BoolExpr.eval, ProfileExpr.eval,
          Common.recordDefault, CommonDefaultRequired.recordShape,
          CommonRecordEnvelope.outsideRecords, CommonDefaultRequired.fieldPresence,
          CommonRecordTailProfiles.initialField, CommonRecordTailProfiles.initialOptional,
          Payload.evalLayer]
        simp_all only
      · simp only [Summary.recordDefault, ite_eq_right active, BoolExpr.eval, ProfileExpr.eval,
          Common.recordDefault, CommonDefaultRequired.recordShape,
          CommonRecordEnvelope.outsideRecords, CommonDefaultRequired.fieldPresence,
          CommonRecordTailProfiles.initialField, CommonRecordTailProfiles.initialOptional]
        simp_all only
  | mask more source ih => exact ih (hidden ++ more)

theorem compile_field_exact (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty)
    (hidden : List Nat) (label : Nat) (source : OpenLayer Rows Node Child) :
    (compile hidden label source).field.eval nodes children =
      CommonPayloadProjection.fieldType hidden label (source.eval rows nodes children) :=
  congrArg Meaning.field (compile_exact rows nodes children hidden label source)

theorem compile_optional_exact (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty)
    (hidden : List Nat) (label : Nat) (source : OpenLayer Rows Node Child) :
    (compile hidden label source).optional.eval nodes children =
      CommonPayloadProjection.optionalType hidden label (source.eval rows nodes children) :=
  congrArg Meaning.optional (compile_exact rows nodes children hidden label source)

theorem compile_presence_exact (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty)
    (hidden : List Nat) (label : Nat) (source : OpenLayer Rows Node Child) :
    (compile hidden label source).present.eval nodes =
      CommonDefaultRequired.fieldPresence hidden label (source.eval rows nodes children) :=
  congrArg Meaning.present (compile_exact rows nodes children hidden label source)

/-- The compiled profile gives every positive-depth field observation, at
every negative rank and demand environment; this is not finite sampling. -/
theorem compile_field_probe_exact (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty)
    (hidden : List Nat) (label : Nat) (source : OpenLayer Rows Node Child)
    (depth rank : Nat) (env : CommonFinite.Environment Row) (obs : Common.Observation) :
    CommonFinite.MaskedProbeAt Common.rowLe rank env hidden
        (Common.observeTy (depth + 1) (source.eval rows nodes children)) (.field label obs) ↔
      CommonPayloadProjection.ProfileAt depth rank env
        ((compile hidden label source).field.eval nodes children) obs := by
  rw [compile_field_exact]
  exact CommonPayloadProjection.field_type_exact hidden label _ depth rank env obs

theorem compile_optional_probe_exact (rows : Rows → Row) (nodes : Node → Ty) (children : Child → Ty)
    (hidden : List Nat) (label : Nat) (source : OpenLayer Rows Node Child)
    (depth rank : Nat) (env : CommonFinite.Environment Row) (obs : Common.Observation) :
    CommonFinite.MaskedProbeAt Common.rowLe rank env hidden
        (Common.observeTy (depth + 1) (source.eval rows nodes children)) (.optional label obs) ↔
      CommonPayloadProjection.ProfileAt depth rank env
        ((compile hidden label source).optional.eval nodes children) obs := by
  rw [compile_optional_exact]
  exact CommonPayloadProjection.optional_type_exact hidden label _ depth rank env obs

end Yulang.CommonSymbolicRecordProfiles
