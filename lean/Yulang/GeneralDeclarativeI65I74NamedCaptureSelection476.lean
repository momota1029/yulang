import Yulang.GeneralDeclarativeI65I74LocatedHeadCapture476
import Yulang.GeneralDeclarativeI65I74BeforeCaptureField475

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open WrittenPattern460.PhysicalOrigin (Pose)
open ObservationSyntax471
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)

structure NamedSelectionWire476 where
  field : Nat
  writtenPath : List Pose
  markOrdinal : Nat

/-- Exact selected field of the separately supplied original source
view. This is a receipt reader, not an issuer or a K2 verdict. -/
structure NamedSelection476 {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) (query : NamedSelectionWire476) where
  field : FieldOrigin (gateFromAttachedAuthor472 (p := p) a) gd
    ((exactFieldWire w r.picked query.field query.writtenPath).atGate a)
  trace : LocatedCapture476 w.offered
  returned : readLocatedAtHead476 r = some trace
  mark : LocatedMark476 w.offered
  chosen : trace.marks[query.markOrdinal]? = some mark
  selectedPath : mark.path = [.field query.field]
  sameNamedChild : field.actualPayload = .variable mark.exposure.name

def readNamedSelection476 {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) (query : NamedSelectionWire476) :
    Option (NamedSelection476 r query) := do
  let found ← readBoundField r query.field query.writtenPath
  match ran : readLocatedAtHead476 r with
  | none => none
  | some trace =>
    match selected : trace.marks[query.markOrdinal]? with
    | none => none
    | some mark =>
      if path : mark.path = [.field query.field] then
        if payload : eqExpr found.actualPayload (.variable mark.exposure.name) = true then
          some ⟨found,trace,ran,mark,selected,path,(eq_expr ..).mp payload⟩
        else none
      else none

theorem exact_given_named_selection_replays476 {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    {q : NamedSelectionWire476} (given : NamedSelection476 r q) :
    readNamedSelection476 r q = some given := by
  rcases given with ⟨field,trace,ran,mark,slot,path,child⟩
  have old := supplied_before_capture_replays_exact_original_field r q.field q.writtenPath field
  have intended := (eq_expr ..).mpr child
  simp only [readNamedSelection476,old,bind,Option.bind]
  split
  · rename_i missed
    rw [ran] at missed
    contradiction
  · rename_i got seen
    have same := Option.some.inj (seen.symm.trans ran)
    subst got
    split
    · rename_i missed
      rw [slot] at missed
      contradiction
    · rename_i got seen
      have same := Option.some.inj (seen.symm.trans slot)
      subst got
      simp [path,intended]

theorem named_selection_exists_exactly_when_finite_reader_succeeds476
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) (q : NamedSelectionWire476) :
    (readNamedSelection476 r q).isSome = true ↔ Nonempty (NamedSelection476 r q) := by
  constructor
  · cases seen : readNamedSelection476 r q with
    | none => simp
    | some parsed => exact fun _ => ⟨parsed⟩
  · rintro ⟨given⟩
    simp [exact_given_named_selection_replays476 given]

theorem checked_field_and_mark_retain_distinct_exact_source_positions476
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {q : NamedSelectionWire476} (given : NamedSelection476 r q) :
    WrittenPattern460.PhysicalOrigin.Origin r.head.orig.original (.field q.field)
      q.writtenPath given.field.sourcePattern ∧
    (rawAt p).equations[given.mark.exposure.picked.raw]? = some given.mark.exposure.picked.row ∧
    t.authored[given.mark.exposure.picked.author]? = some given.mark.exposure.picked.row ∧
    given.mark.exposure.picked.row.left = given.mark.exposure.name ∧
    given.field.actualPayload = .variable given.mark.exposure.name := by
  have same := (forwarded_old_read_uses_the_very_same_prechecked_head_and_row
    r q.field q.writtenPath given.field).1
  have selected := given.field.selectedWritten
  change WrittenPattern460.PhysicalOrigin.Origin given.field.head.orig.original
    (.field q.field) q.writtenPath given.field.sourcePattern at selected
  rw [same] at selected
  obtain ⟨raw,author,owner⟩ := a_marked_name_exposure_keeps_both_exact_original_rows r given.mark.exposure
  exact ⟨selected,raw,author,owner,given.sameNamedChild⟩

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
