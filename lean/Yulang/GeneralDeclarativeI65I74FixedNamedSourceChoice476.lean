import Yulang.GeneralDeclarativeI65I74NamedCaptureSelection476

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open WrittenPattern460.PhysicalOrigin (Pose)
open ObservationSyntax471 (FieldOrigin gateFromAttachedAuthor472)

/-- The separate typed source choice to which a trace must be joined.
It is supplied, not minted by a mark list. Its field is an old exact
authored receipt on the same original problem and original frame. -/
structure FixedFieldChoice476 {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) where
  label : Nat
  path : List Pose
  original : FieldOrigin (gateFromAttachedAuthor472 (p := p) a) gd
    ((exactFieldWire w r.picked label path).atGate a)

def checkFixedFieldChoice476 {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) (label : Nat) (path : List Pose) :
    Option (FixedFieldChoice476 r) :=
  (readBoundField r label path).map (fun given => ⟨label,path,given⟩)

def readNamedAtFixedChoice476 {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} (fixed : FixedFieldChoice476 r) (q : NamedSelectionWire476) :
    Option (NamedSelection476 r q) :=
  if q.field = fixed.label ∧ q.writtenPath = fixed.path then readNamedSelection476 r q else none

theorem original_fixed_field_replays_in_same_input476
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} (fixed : FixedFieldChoice476 r) :
    checkFixedFieldChoice476 r fixed.label fixed.path = some fixed := by
  cases fixed with
  | mk label path original =>
    simp [checkFixedFieldChoice476,supplied_before_capture_replays_exact_original_field r label path original]

theorem fixed_named_join_is_exact_same_literal_field_receipt476
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} (fixed : FixedFieldChoice476 r) (q : NamedSelectionWire476)
    (result : NamedSelection476 r q) :
    readNamedAtFixedChoice476 fixed q = some result ↔
      q.field = fixed.label ∧ q.writtenPath = fixed.path ∧ HEq result.field fixed.original := by
  constructor
  · intro hit
    by_cases same : q.field = fixed.label ∧ q.writtenPath = fixed.path
    · refine ⟨same.1,same.2,?_⟩
      have fromRead := supplied_before_capture_replays_exact_original_field r q.field q.writtenPath result.field
      have fromOld := supplied_before_capture_replays_exact_original_field r fixed.label fixed.path fixed.original
      cases q with
      | mk field writtenPath markOrdinal =>
        dsimp at same
        obtain ⟨rfl,rfl⟩ := same
        exact heq_of_eq (Option.some.inj (fromRead.symm.trans fromOld))
    · simp [readNamedAtFixedChoice476,same] at hit
  · rintro ⟨field,path,_⟩
    simp [readNamedAtFixedChoice476,field,path,exact_given_named_selection_replays476 result]

theorem wrong_original_label_or_path_cannot_use_a_fixed_receipt476
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} (fixed : FixedFieldChoice476 r) (q : NamedSelectionWire476)
    (wrong : q.field ≠ fixed.label ∨ q.writtenPath ≠ fixed.path) :
    readNamedAtFixedChoice476 fixed q = none := by
  rcases wrong with bad|bad <;> simp [readNamedAtFixedChoice476,bad]

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
