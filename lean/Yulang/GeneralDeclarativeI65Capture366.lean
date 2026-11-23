import Yulang.GeneralDeclarativeI65State365

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open Core.PresenceGeneration (TyTerm RowTerm)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeBounds319 (Bound bound_sound)
open CommonNominalFullCarrier (Equivalent Subtype)
open PresenceNormalForm (Atom)

/-- A value payload pair as originally observed at two argument
positions. Only the two endpoints participate in the head match. -/
structure ValueBind (s : State) (b : Capture) (l h : TyTerm Nat) : Prop where
  lowToSlot : Atom.tyLe l (.var b.lower) ∈ s.current.ordinary.normal.ordinary
  slotToLow : Atom.tyLe (.var b.lower) l ∈ s.current.ordinary.normal.ordinary
  highToSlot : Atom.tyLe h (.var b.upper) ∈ s.current.ordinary.normal.ordinary
  slotToHigh : Atom.tyLe (.var b.upper) h ∈ s.current.ordinary.normal.ordinary

structure RowBind (s : State) (b : Capture) (l h : RowTerm Nat) : Prop where
  lowToSlot : Atom.rowLe l (.var b.lower) ∈ s.current.ordinary.normal.ordinary
  slotToLow : Atom.rowLe (.var b.lower) l ∈ s.current.ordinary.normal.ordinary
  highToSlot : Atom.rowLe h (.var b.upper) ∈ s.current.ordinary.normal.ordinary
  slotToHigh : Atom.rowLe (.var b.upper) h ∈ s.current.ordinary.normal.ordinary

def valueAt (m : Model) (t : TyTerm Nat) :=
  t.eval CommonNominalFullCarrier.model m.assignment

def rowAt (m : Model) (t : RowTerm Nat) :=
  t.eval CommonNominalFullCarrier.model m.assignment

theorem value_binding_sound {s : State} {b : Capture} {l h : TyTerm Nat}
    (read : ValueBind s b l h) (m : Model) (fit : Fits s m) :
    Equivalent (valueAt m l) (m.assignment b.lower).1 ∧
    Equivalent (valueAt m h) (m.assignment b.upper).1 :=
  ⟨⟨fit.1.1.1.1 _ read.lowToSlot,fit.1.1.1.1 _ read.slotToLow⟩,
    ⟨fit.1.1.1.1 _ read.highToSlot,fit.1.1.1.1 _ read.slotToHigh⟩⟩

theorem row_binding_sound {s : State} {b : Capture} {l h : RowTerm Nat}
    (read : RowBind s b l h) (m : Model) (fit : Fits s m) :
    (Common.rowLe (rowAt m l) (m.assignment b.lower).2 ∧ Common.rowLe (m.assignment b.lower).2 (rowAt m l)) ∧
    (Common.rowLe (rowAt m h) (m.assignment b.upper).2 ∧ Common.rowLe (m.assignment b.upper).2 (rowAt m h)) :=
  ⟨⟨fit.1.1.1.1 _ read.lowToSlot,fit.1.1.1.1 _ read.slotToLow⟩,
    ⟨fit.1.1.1.1 _ read.highToSlot,fit.1.1.1.1 _ read.slotToHigh⟩⟩

/-- This proposition is intentionally separate from ValueBind and
RowBind. The real binder center is read for the selected source/body,
not chosen from overlapping bounds in a head test. -/
structure SelectedCenters (s : State) (logical compiled : Capture) : Prop where
  actualName : logical.center = compiled.center
  logicalBounds : GeneralDeclarativeDemand320.Bounds s.current.ordinary logical
  compiledBounds : GeneralDeclarativeDemand320.Bounds s.current.ordinary compiled

theorem selected_centers_sound {s : State} {logical compiled : Capture}
    (read : SelectedCenters s logical compiled) (m : Model) (fit : Fits s m) :
    (m.assignment logical.center).1 = (m.assignment compiled.center).1 ∧
    GeneralDeclarativeWhere319.InInterval (m.assignment logical.lower).1
      (m.assignment logical.upper).1 (m.assignment logical.center).1 ∧
    GeneralDeclarativeWhere319.InInterval (m.assignment compiled.lower).1
      (m.assignment compiled.upper).1 (m.assignment compiled.center).1 :=
  ⟨congrArg (fun n => (m.assignment n).1) read.actualName,
    GeneralDeclarativeDemand320.bounds_sound read.logicalBounds m.assignment fit.1.1,
    GeneralDeclarativeDemand320.bounds_sound read.compiledBounds m.assignment fit.1.1⟩

end Yulang.GeneralDeclarativeI65
