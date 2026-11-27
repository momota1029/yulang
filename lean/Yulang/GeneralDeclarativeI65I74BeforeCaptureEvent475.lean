import Yulang.GeneralDeclarativeI65I74InputCoordinates475
import Yulang.GeneralDeclarativeI65I74ActualHeadFrame467

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (HeadAddress CheckedTable PrecheckedHead
  readPrecheckedHead each_prechecked_head_position_replays)
open ActualHeadFrame467 (actualCompilerFrameKey
  a_single_visible_compiler_head_has_exactly_its_own_unfiltered_source_index)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)

/-- A caller-supplied ordered view of original source rows. This wire
does not create the author table, choose a candidate, or allocate names. -/
structure BeforeCaptureWire where
  source : HeadAddress
  frame : FrameKey
  offered : List StampedRead

def FirstIs (n : Nat) (offered : List StampedRead) (row : StampedRead) : Prop :=
  row.row.left = n ∧
  ∃ before after, offered = before ++ row :: after ∧ ∀ other ∈ before, other.row.left ≠ n

theorem first_is_exact {n : Nat} {offered : List StampedRead} {row : StampedRead} :
    first n offered = some row ↔ FirstIs n offered row := by
  unfold first FirstIs
  rw [List.find?_eq_some_iff_append]
  simp

abbrev rawAt (p : FullProblem) := p.state.base.core.current.ordinary
abbrev registryAt (p : FullProblem) := p.old.state.core.current.environment.source.declarations

/-- A receipt is indexed by the original problem, retained attachment,
and the literal caller wire. The frame is the exact authored read, not
a stand-in for a release token, revision or native output. -/
structure BeforeCapture {p : FullProblem} {t : Table} (a : Attached (rawAt p) t)
    (gd : CheckedTable p.old.state.core.current) (w : BeforeCaptureWire) where
  head : PrecheckedHead (p := p.old) gd
  address : head.orig.location = w.source
  visibleOnce : (GeneralDeclarativeI65.visible p.old.state.core p.old.root).length = 1
  frame : actualCompilerFrameKey head.orig = some w.frame
  checked : valid (rawAt p).equations t.authored w.offered = true
  picked : StampedRead
  firstAt : FirstIs head.orig.capture.lower w.offered picked

def readBeforeCapture {p : FullProblem} {t : Table} (a : Attached (rawAt p) t)
    (gd : CheckedTable p.old.state.core.current) (w : BeforeCaptureWire) :
    Option (BeforeCapture a gd w) := do
  let head ← readPrecheckedHead (p := p.old) gd w.source
  if address : head.orig.location = w.source then
    if one : (GeneralDeclarativeI65.visible p.old.state.core p.old.root).length = 1 then
      if frame : actualCompilerFrameKey head.orig = some w.frame then
        if data : valid (rawAt p).equations t.authored w.offered = true then
          match picked : first head.orig.capture.lower w.offered with
          | none => none
          | some row => some ⟨head,address,one,frame,data,row,first_is_exact.mp picked⟩
        else none
      else none
    else none
  else none

theorem exact_before_capture_replays {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} (r : BeforeCapture a gd w) :
    readBeforeCapture a gd w = some r := by
  rcases r with ⟨head,address,one,frame,checked,picked,firstAt⟩
  have headRead := each_prechecked_head_position_replays gd head
  rw [address] at headRead
  have found := first_is_exact.mpr firstAt
  simp only [readBeforeCapture,headRead,address,one,frame,checked,bind,Option.bind,dite_true]
  split <;> simp_all

theorem finite_original_before_capture_iff {p : FullProblem} {t : Table} (a : Attached (rawAt p) t)
    (gd : CheckedTable p.old.state.core.current) (w : BeforeCaptureWire) :
    (readBeforeCapture a gd w).isSome = true ↔ Nonempty (BeforeCapture a gd w) := by
  constructor
  · cases h : readBeforeCapture a gd w with
    | none => simp
    | some r => exact fun _ => ⟨r⟩
  · rintro ⟨r⟩
    simp [exact_before_capture_replays r]

theorem literal_frame_and_input_rows_before_any_capture {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} (r : BeforeCapture a gd w) :
    w.frame.occurrence = p.old.root.occurrence ∧
    w.frame.declaration = r.head.orig.declaration.id ∧
    (registryAt p)[w.frame.sourceOrdinal]? = some r.head.orig.declaration ∧
    (rawAt p).equations[r.picked.raw]? = some r.picked.row ∧
    t.authored[r.picked.author]? = some r.picked.row ∧
    r.picked.row.left = r.head.orig.capture.lower := by
  obtain ⟨i,ord,sourceAt,_⟩ :=
    a_single_visible_compiler_head_has_exactly_its_own_unfiltered_source_index
      r.head.orig r.visibleOnce
  have stamp : w.frame = ⟨p.old.root.occurrence,r.head.orig.declaration.id,i⟩ :=
    Option.some.inj (r.frame.symm.trans (by simp [actualCompilerFrameKey,ord]))
  have exactRows := first_uses_two_actual_coordinates _ _ _ r.checked (first_is_exact.mpr r.firstAt)
  exact ⟨by simp [stamp],by simp [stamp],by simpa [stamp,registryAt] using sourceAt,exactRows⟩

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
