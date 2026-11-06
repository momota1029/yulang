import Yulang.RigidRecordViews

/-!
# Normal forms of structural atom paths

Non-record atoms retain their constructor and compare their components.
Record paths into a target without a proper-spine view consist solely of
same-label congruence steps. The one-way rigid-target tail rule always lands
in a proper spine, so it cannot be used on such a path.
-/

namespace Yulang.RigidRecordAtomNormal

open StructuralBase (Ty IsRecord)
open RigidSemanticRecords (Subtype Equivalent)
open RigidRecordAtoms (Atomic Step Chain)
open RigidRecordViews (View)

universe u

variable {Row : Type u} {leRow : Row → Row → Prop}

def RecordAtom : Ty Row → Prop
  | .emptyRecord | .record _ _ _ => True
  | _ => False

theorem isRecord_atom {type : Ty Row} (shape : IsRecord type) : RecordAtom type := by
  cases shape <;> trivial

inductive ShapeComparison (leRow : Row → Row → Prop) : Ty Row → Ty Row → Prop where
  | base : ShapeComparison leRow (.base value) (.base value)
  | pair : Subtype leRow a a' → Subtype leRow b b' →
      ShapeComparison leRow (.pair a b) (.pair a' b')
  | variant : Subtype leRow a b →
      ShapeComparison leRow (.variant label a) (.variant label b)
  | arrow : Subtype leRow input' input → leRow inputRow' inputRow →
      Subtype leRow output output' → leRow outputRow outputRow' →
      ShapeComparison leRow (.arrow input inputRow output outputRow)
        (.arrow input' inputRow' output' outputRow')
  | records : RecordAtom source → RecordAtom target → ShapeComparison leRow source target

theorem ShapeComparison.refl (rowRefl : ∀ row, leRow row row)
    {type : Ty Row} (atom : Atomic type) : ShapeComparison leRow type type := by
  cases type with
  | base => exact .base
  | pair => exact .pair (.refl _) (.refl _)
  | variant => exact .variant (.refl _)
  | arrow => exact .arrow (.refl _) (rowRefl _) (.refl _) (rowRefl _)
  | emptyRecord | record => exact .records trivial trivial
  | _ => cases atom

theorem ShapeComparison.trans
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    {a b c : Ty Row} (first : ShapeComparison leRow a b) (last : ShapeComparison leRow b c) :
    ShapeComparison leRow a c := by
  cases first with
  | base =>
      cases last with
      | base => exact .base
      | records shape => cases shape
  | pair left right =>
      cases last with
      | pair nextLeft nextRight => exact .pair (.trans left nextLeft) (.trans right nextRight)
      | records shape => cases shape
  | variant payload =>
      cases last with
      | variant next => exact .variant (.trans payload next)
      | records shape => cases shape
  | arrow input inputRow output outputRow =>
      cases last with
      | arrow nextInput nextInputRow nextOutput nextOutputRow =>
          exact .arrow (.trans nextInput input) (rowTrans nextInputRow inputRow)
            (.trans output nextOutput) (rowTrans outputRow nextOutputRow)
      | records shape => cases shape
  | records source middle =>
      cases last with
      | base | pair | variant | arrow => cases middle
      | records _ target => exact .records source target

theorem Step.shape {a b : Ty Row} (step : Step leRow a b) : ShapeComparison leRow a b := by
  cases step with
  | pair first last => exact .pair first last
  | variant payload => exact .variant payload
  | arrow input inputRow output outputRow => exact .arrow input inputRow output outputRow
  | record source target => exact .records (isRecord_atom source) (isRecord_atom target)
  | recordCongr => exact .records trivial trivial
  | recordTail => exact .records trivial trivial

theorem Chain.shape (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    {a b : Ty Row} (chain : Chain leRow a b) : ShapeComparison leRow a b := by
  induction chain with
  | refl atom => exact .refl rowRefl atom
  | step one => exact Step.shape one
  | trans _ _ first last => exact ShapeComparison.trans (leRow := leRow) rowTrans first last

def RawRecord : Ty Row → Prop
  | .record _ _ _ => True
  | _ => False

inductive HeadCongruent (leRow : Row → Row → Prop) : Ty Row → Ty Row → Prop where
  | field : Equivalent leRow a b → Equivalent leRow r s →
      HeadCongruent leRow (.record label a r) (.record label b s)

theorem HeadCongruent.refl {type : Ty Row} (raw : RawRecord type) :
    HeadCongruent leRow type type := by
  cases type with
  | record => exact .field (.refl _) (.refl _)
  | _ => cases raw

theorem HeadCongruent.trans {a b c : Ty Row}
    (first : HeadCongruent leRow a b) (last : HeadCongruent leRow b c) : HeadCongruent leRow a c := by
  cases first with
  | field head tail =>
      cases last with
      | field nextHead nextTail => exact .field (head.trans nextHead) (tail.trans nextTail)

theorem HeadCongruent.source_raw {a b : Ty Row}
    (same : HeadCongruent leRow a b) : RawRecord a := by
  cases same
  trivial

theorem HeadCongruent.target_raw {a b : Ty Row}
    (same : HeadCongruent leRow a b) : RawRecord b := by
  cases same
  trivial

theorem Step.opaque_target {a b : Ty Row} (step : Step leRow a b) (raw : RawRecord b)
    (noView : ¬ ∃ fields, View leRow b fields) : HeadCongruent leRow a b := by
  cases step with
  | pair | variant | arrow => cases raw
  | record _ target => exact False.elim (noView (RigidRecordViews.record_has_view target))
  | recordCongr head tail => exact .field head tail
  | recordTail rigid _ => exact False.elim (noView (RigidRecordViews.record_has_view (.field rigid)))

theorem Chain.opaque_target {a b : Ty Row} (chain : Chain leRow a b) (raw : RawRecord b)
    (noView : ¬ ∃ fields, View leRow b fields) : HeadCongruent leRow a b := by
  induction chain with
  | refl => exact .refl raw
  | step one => exact Step.opaque_target one raw noView
  | trans first last firstIH lastIH =>
      have between := lastIH raw noView
      have missing : ¬ ∃ fields, View leRow _ fields :=
        fun existsView => noView (RigidRecordViews.Chain.view_forward last existsView)
      exact (firstIH between.source_raw missing).trans between

end Yulang.RigidRecordAtomNormal
