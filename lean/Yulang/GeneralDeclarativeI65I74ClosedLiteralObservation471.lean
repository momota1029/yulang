import Yulang.GeneralDeclarativeI65I74LiteralFoldInputTyping471
import Yulang.GeneralDeclarativeI65I74FiniteObservationQuotient471

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.LiteralFold471
open RetainedFull445
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleRegularGraph (Graph Node)
open QuotientObservation471

/-- The fully described narrow observation region: no ambient aliases or
other rows that could change how one of the two names is observed. The
three Fin keys below are view indices, not new raw names. -/
structure ClosedLiteralRegion {p : FullProblem} {g : SourceGate p}
    {tab : CheckedTable p.old.state.core.current} {w : SourceWire g} (r : SourceReceipt g tab w) : Type where
  normalEmpty : p.state.base.core.current.ordinary.normal.ordinary = []
  intervalsEmpty : p.state.base.core.current.ordinary.normal.intervals = []
  rawRows : p.state.base.core.current.ordinary.equations = [r.field.folded.owner,r.field.folded.point]
  distinctNames : r.field.folded.owner.left ≠ r.field.folded.point.left

def readClosedLiteralRegion {p g tab w} (r : @SourceReceipt p g tab w) :
    Option (ClosedLiteralRegion r) :=
  let raw := p.state.base.core.current.ordinary
  if yes : raw.normal.ordinary = [] ∧ raw.normal.intervals = [] ∧ raw.equations.length = 2 ∧
          w.field.physical.ownerOrdinal = 0 ∧ w.field.physical.pointOrdinal = 1 ∧
          r.field.folded.owner.left ≠ r.field.folded.point.left then
    have head : raw.equations[0]'(yes.2.2.1 ▸ by decide) = r.field.folded.owner := by
      have read := r.field.folded.selectedOwner
      rw [yes.2.2.2.1] at read
      exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans read)
    have next : raw.equations[1]'(yes.2.2.1 ▸ by decide) = r.field.folded.point := by
      have read := r.field.folded.selectedPoint
      rw [yes.2.2.2.2.1] at read
      exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans read)
    some ⟨yes.1,yes.2.1,by rw [List.eq_getElem_of_length_eq_two _ yes.2.2.1,head,next],
      yes.2.2.2.2.2⟩
  else none

def fullObservation (outer inner : Nat) : Graph 3 :=
  #v[.structural outer [1],.structural inner [2],.structural inner [2]].get

/-- Every stored constructor used by this view is accounted for, including
the exact source payload/representative, not just a claimed equal value. -/
theorem closed_literal_region_books_every_constructor {p g tab w}
    (r : @SourceReceipt p g tab w) (region : ClosedLiteralRegion r) :
    p.state.base.core.current.ordinary.equations = [r.field.folded.owner,r.field.folded.point] ∧
    r.field.folded.owner.right = .record r.field.folded.field r.field.folded.inline
      (.primitive .emptyRecord []) ∧
    r.field.folded.inline = .record w.field.label (.variable r.field.folded.point.left)
      (.primitive .emptyRecord []) ∧
    r.field.folded.point.right = .record w.field.label (.variable r.field.folded.point.left)
      (.primitive .emptyRecord []) :=
  ⟨region.rawRows,readFirstClosedField_shape r.field.folded.fieldAtSource,
    r.field.folded.unfolded.trans (readFirstClosedField_shape r.field.namedConstructor),
    readFirstClosedField_shape r.field.namedConstructor⟩

structure ObservationPacket where
  report : SourceReport
  argumentOnCycle : Bool
  fieldOnCycle : Bool
  deriving DecidableEq

def readExactObservation {p : FullProblem} (g : SourceGate p)
    (tab : CheckedTable p.old.state.core.current) (w : SourceWire g)
    (partition : QuotientObservation471.Wire 3 k) : Option ObservationPacket := do
  let ⟨r,_typing⟩ ← readSameInputTyping g tab w
  let _complete ← readClosedLiteralRegion r
  let graph := fullObservation r.field.folded.field w.field.label
  let argument ← QuotientObservation471.replay graph 0 partition
  let field ← QuotientObservation471.replay graph 1 partition
  pure ⟨reportOfSource r,argument,field⟩

theorem exact_observation_returns_checked_same_graph_cycle_bits {p : FullProblem} {g : SourceGate p}
    {tab : CheckedTable p.old.state.core.current} {w : SourceWire g} {k : Nat}
    {partition : QuotientObservation471.Wire 3 k} {packet}
    (ok : readExactObservation g tab w partition = some packet) :
    ∃ (r : SourceReceipt g tab w) (_t : InputTypingEvent r) (_region : ClosedLiteralRegion r),
      packet.report = reportOfSource r ∧
      (packet.argumentOnCycle = true ↔
        ReturnsUpToEquality (fullObservation r.field.folded.field w.field.label) 0) ∧
      (packet.fieldOnCycle = true ↔
        ReturnsUpToEquality (fullObservation r.field.folded.field w.field.label) 1) := by
  unfold readExactObservation at ok
  cases event : readSameInputTyping g tab w with
  | none => simp [event,bind,Option.bind] at ok
  | some got =>
    obtain ⟨r,t⟩ := got
    cases complete : readClosedLiteralRegion r with
    | none => simp [event,complete,bind,Option.bind] at ok
    | some region =>
      cases a : QuotientObservation471.replay (fullObservation r.field.folded.field w.field.label) 0 partition with
      | none => simp [event,complete,bind,Option.bind,a] at ok
      | some argument =>
        cases b : QuotientObservation471.replay (fullObservation r.field.folded.field w.field.label) 1 partition with
        | none => simp [event,complete,bind,Option.bind,a,b] at ok
        | some field =>
          have matchPacket : (⟨reportOfSource r,argument,field⟩ : ObservationPacket) = packet := by
            simpa [event,complete,bind,Option.bind,a,b] using ok
          subst packet
          refine ⟨r,t,region,rfl,?_,?_⟩
          · cases argument
            · have z := safe_replay_exact.mp a
              simp [show ¬ReturnsUpToEquality (fullObservation r.field.folded.field w.field.label) 0 from fun x =>
                z.2 ((quotient_cycle_iff_returns_up_to_equality z.1 _).mpr x)]
            · have z := positive_replay_exact.mp a
              simp [(quotient_cycle_iff_returns_up_to_equality z.1 _).mp z.2]
          · cases field
            · have z := safe_replay_exact.mp b
              simp [show ¬ReturnsUpToEquality (fullObservation r.field.folded.field w.field.label) 1 from fun x =>
                z.2 ((quotient_cycle_iff_returns_up_to_equality z.1 _).mpr x)]
            · have z := positive_replay_exact.mp b
              simp [(quotient_cycle_iff_returns_up_to_equality z.1 _).mp z.2]

end Yulang.GeneralDeclarativeI65.I72.LiteralFold471
