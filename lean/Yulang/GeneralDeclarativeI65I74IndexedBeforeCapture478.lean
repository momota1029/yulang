import Yulang.GeneralDeclarativeI65I74SourceIndexPair478

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open PreparedDeclarations463 (HeadAddress CheckedTable readPrecheckedHead each_prechecked_head_position_replays)
open ActualHeadFrame467 (actualCompilerFrameKey)

/-- Minimal coordinate packet for the old capture-input adapter.
The caller still supplies the event's independently authenticated
row-address pairs and their existing author table. -/
structure IndexedBeforeCapture478 where
  head : HeadAddress
  rows : List SourceIndexPair478

def BeforeCaptureWire.indexed478 (w : BeforeCaptureWire) : IndexedBeforeCapture478 :=
  ⟨w.source,w.offered.map StampedRead.indexPair478⟩

def recoverBeforeCaptureWire478 (p : FullProblem) (t : Table)
    (gd : CheckedTable p.old.state.core.current) (q : IndexedBeforeCapture478) : Option BeforeCaptureWire := do
  let h ← readPrecheckedHead (p := p.old) gd q.head
  let f ← actualCompilerFrameKey h.orig
  let rows ← recoverOldStamps478 (rawAt p).equations t.authored q.rows
  pure ⟨q.head,f,rows⟩

def readIndexedBeforeCapture478 {p : FullProblem} {t : Table} (a : Attached (rawAt p) t)
    (gd : CheckedTable p.old.state.core.current) (q : IndexedBeforeCapture478) :
    Option (Σ original : BeforeCaptureWire, BeforeCapture a gd original) := do
  let original ← recoverBeforeCaptureWire478 p t gd q
  let result ← readBeforeCapture a gd original
  pure ⟨original,result⟩

theorem recovering_from_exact_input_indices_keeps_frame_and_actual_capture478
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire} (real : BeforeCapture a gd w) :
    readIndexedBeforeCapture478 a gd w.indexed478 = some ⟨w,real⟩ := by
  have source := each_prechecked_head_position_replays gd real.head
  rw [real.address] at source
  have exactRows := (erasing_duplicate_row_payload_fields_loses_no_old_ordered_read478 _ _ _).mpr real.checked
  have restored : recoverBeforeCaptureWire478 p t gd w.indexed478 = some w := by
    rcases w with ⟨address,frame,rows⟩
    simp [recoverBeforeCaptureWire478,BeforeCaptureWire.indexed478,source,real.frame,exactRows]
  simp [readIndexedBeforeCapture478,restored,exact_before_capture_replays real]

theorem recovered_wire_has_exactly_the_supplied_old_index_packet478
    {p : FullProblem} {t : Table} {gd : CheckedTable p.old.state.core.current}
    {q : IndexedBeforeCapture478} {w : BeforeCaptureWire}
    (read : recoverBeforeCaptureWire478 p t gd q = some w) :
    w.source = q.head ∧ w.offered.map StampedRead.indexPair478 = q.rows := by
  unfold recoverBeforeCaptureWire478 at read
  cases h : readPrecheckedHead (p := p.old) gd q.head with
  | none => simp [h] at read
  | some head =>
    cases f : actualCompilerFrameKey head.orig with
    | none => simp [h,f] at read
    | some frame =>
      cases rows : recoverOldStamps478 (rawAt p).equations t.authored q.rows with
      | none => simp [h,rows] at read
      | some offered =>
        have same : (⟨q.head,frame,offered⟩ : BeforeCaptureWire) = w := by
          simpa [h,f,rows] using read
        subst w
        exact ⟨rfl,recovery_never_reorders_original_pairs478 rows⟩

theorem old_before_capture_exists_exactly_from_the_same_indexed_input478
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} (q : IndexedBeforeCapture478) :
    (readIndexedBeforeCapture478 a gd q).isSome = true ↔
      ∃ w : BeforeCaptureWire, w.indexed478 = q ∧ Nonempty (BeforeCapture a gd w) := by
  constructor
  · intro hit
    unfold readIndexedBeforeCapture478 at hit
    cases got : recoverBeforeCaptureWire478 p t gd q with
    | none => simp [got] at hit
    | some w =>
      cases found : readBeforeCapture a gd w with
      | none => simp [got,found] at hit
      | some actual =>
        obtain ⟨head,rows⟩ := recovered_wire_has_exactly_the_supplied_old_index_packet478 got
        refine ⟨w,?_,⟨actual⟩⟩
        rcases q
        simp_all [BeforeCaptureWire.indexed478]
  · rintro ⟨w,identity,⟨actual⟩⟩
    rw [←identity,recovering_from_exact_input_indices_keeps_frame_and_actual_capture478 actual]
    rfl

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
