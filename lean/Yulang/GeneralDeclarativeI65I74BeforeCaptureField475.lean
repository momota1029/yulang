import Yulang.GeneralDeclarativeI65I74BeforeCaptureEvent475

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable each_prechecked_head_position_replays)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open ObservationSyntax471 (AttachedFieldWire472 FieldOrigin gateFromAttachedAuthor472
  readFieldOrigin readTyping SourceTyping)
open WrittenPattern460.PhysicalOrigin (Pose)

def exactFieldWire (w : BeforeCaptureWire) (pin : StampedRead) (label : Nat) (path : List Pose) :
    AttachedFieldWire472 :=
  ⟨w.source,w.frame.sourceOrdinal,label,path,pin.raw,pin.author⟩

/-- Forward exactly the two retained row positions from the preceding
supplied source-view event. Source field selection still uses the old
logical/written visitor and may fail; no verdict follows from failure. -/
def readBoundField {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} (r : BeforeCapture a gd w) (label : Nat) (path : List Pose) :
    Option (FieldOrigin (gateFromAttachedAuthor472 (p := p) a) gd
      ((exactFieldWire w r.picked label path).atGate a)) :=
  readFieldOrigin (gateFromAttachedAuthor472 (p := p) a) gd
    ((exactFieldWire w r.picked label path).atGate a)

theorem forwarded_old_read_uses_the_very_same_prechecked_head_and_row {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} (r : BeforeCapture a gd w) (label : Nat) (path : List Pose)
    (f : FieldOrigin (gateFromAttachedAuthor472 (p := p) a) gd
      ((exactFieldWire w r.picked label path).atGate a)) :
    f.head = r.head ∧ f.row = r.picked.row := by
  have old := each_prechecked_head_position_replays gd f.head
  have new := each_prechecked_head_position_replays gd r.head
  have same := f.sourceAddress
  change f.head.orig.location = w.source at same
  rw [same] at old
  rw [r.address] at new
  have got := f.exactRow
  change (rawAt p).equations[r.picked.raw]? = some f.row at got
  have expected := (literal_frame_and_input_rows_before_any_capture r).2.2.2.1
  exact ⟨Option.some.inj (old.symm.trans new),Option.some.inj (got.symm.trans expected)⟩

theorem supplied_before_capture_replays_exact_original_field {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} (r : BeforeCapture a gd w) (label : Nat) (path : List Pose)
    (f : FieldOrigin (gateFromAttachedAuthor472 (p := p) a) gd
      ((exactFieldWire w r.picked label path).atGate a)) :
    readBoundField r label path = some f := by
  exact ObservationSyntax471.independent_source_field_origin_replays f
    ((ObservationSyntax471.attached_author_wire_checks_both_literal_ordinals472 a).mpr
      (by
        have eq := forwarded_old_read_uses_the_very_same_prechecked_head_and_row r label path f
        have facts := literal_frame_and_input_rows_before_any_capture r
        exact ⟨rfl,by simpa [exactFieldWire, AttachedFieldWire472.atGate,eq.2] using facts.2.2.2.1,
          by simpa [exactFieldWire, AttachedFieldWire472.atGate,eq.2] using facts.2.2.2.2.1⟩))

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
