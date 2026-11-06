import Yulang.RigidRecordAtoms

/-!
# Proper record views in the rigid-target tail relation

Views identify atoms with proper spines through semantic equivalence. The
new one-way tail rule preserves views forward, but not backward. This is
why the comparison algorithm searches for a view of the demanded type.
-/

namespace Yulang.RigidRecordViews

open StructuralBase (Ty IsRecord)
open RigidSemanticRecords (Subtype Equivalent)
open RigidRecordAtoms (Atomic Step Chain)

universe u
variable {Row : Type u} {leRow : Row → Row → Prop}

abbrev Fields (Row : Type u) := List (Nat × Ty Row)

def spine : Fields Row → Ty Row
  | [] => .emptyRecord
  | (label, value) :: rest => .record label value (spine rest)

theorem spine_record (fields : Fields Row) : IsRecord (spine fields) := by
  induction fields with
  | nil => exact .empty
  | cons field rest ih => exact .field ih

inductive View (leRow : Row → Row → Prop) : Ty Row → Fields Row → Prop where
  | empty : View leRow .emptyRecord []
  | field : Equivalent leRow rest (spine tail) →
      View leRow (.record label value rest) ((label, value) :: tail)

theorem View.atomic {type : Ty Row} {fields : Fields Row}
    (view : View leRow type fields) : Atomic type := by
  cases view <;> trivial

theorem View.equivalent {type : Ty Row} {fields : Fields Row}
    (view : View leRow type fields) : Equivalent leRow type (spine fields) := by
  cases view with
  | empty => exact .refl _
  | field tail => exact RigidSemanticRecords.record_congr _ (.refl _) tail

theorem record_has_view {type : Ty Row} (shape : IsRecord type) :
    ∃ fields, View leRow type fields := by
  induction shape with
  | empty => exact ⟨[], .empty⟩
  | @field rest label value shape ih =>
      obtain ⟨tail, view⟩ := ih
      exact ⟨(label, value) :: tail, .field view.equivalent⟩

theorem Step.view_forward {source target : Ty Row} (step : Step leRow source target)
    (view : ∃ fields, View leRow source fields) : ∃ fields, View leRow target fields := by
  obtain ⟨fields, view⟩ := view
  cases step with
  | pair => cases view
  | variant => cases view
  | arrow => cases view
  | record _ target => exact record_has_view target
  | recordCongr head tail =>
      cases view with
      | field previous => exact ⟨_, .field (tail.symm.trans previous)⟩
  | recordTail rigid _ => exact record_has_view (.field rigid)

theorem Chain.view_forward {source target : Ty Row} (chain : Chain leRow source target)
    (view : ∃ fields, View leRow source fields) : ∃ fields, View leRow target fields := by
  induction chain with
  | refl => exact view
  | step one => exact Step.view_forward one view
  | trans _ _ first last => exact last (first view)

theorem View.comparison_exact {source target : Ty Row} {left right : Fields Row}
    (sourceView : View leRow source left) (targetView : View leRow target right) :
    Subtype leRow source target ↔ Subtype leRow (spine left) (spine right) :=
  ⟨fun below => .trans sourceView.equivalent.2 (.trans below targetView.equivalent.1),
    fun below => .trans sourceView.equivalent.1 (.trans below targetView.equivalent.2)⟩

/-- A semantic proper-record representative can always be found among the
finite outer atoms of the original tail. The representative's field values
remain the values occurring in its record prefix and semantic tail view. -/
theorem equivalent_proper_atom {type proper : Ty Row} (shape : IsRecord proper)
    (same : Equivalent leRow type proper) :
    ∃ atom ∈ RigidRecordAtoms.atoms type,
      (∃ fields, View leRow atom fields) ∧ Equivalent leRow type atom := by
  obtain ⟨atom, member, equivalent⟩ :=
    RigidRecordAtoms.equivalent_atomic_witness (RigidRecordAtoms.isRecord_atomic shape) same
  have chain := (RigidRecordAtoms.atomic_iff_chain
    (RigidRecordAtoms.isRecord_atomic shape) (RigidRecordAtoms.mem_atoms_atomic member)).mp equivalent.2
  exact ⟨atom, member, Chain.view_forward chain (record_has_view shape), same.trans equivalent.symm⟩

end Yulang.RigidRecordViews
