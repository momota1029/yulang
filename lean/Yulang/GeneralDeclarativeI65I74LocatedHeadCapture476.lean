import Yulang.GeneralDeclarativeI65I74LocatedCaptureErasure476

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open GeneralDeclarativeNestedDecode332 (decode)
open GeneralDeclarativeTermWalk322 (Walk)

def readLocatedAtHead476 {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) : Option (LocatedCapture476 w.offered) :=
  if legacyCodeMatches p r.head.orig then do
    let target ← decode r.head.orig.code
    runLocated476 w.offered [] .actual (.variable r.head.orig.capture.lower) target.val
  else none

theorem located_at_head_erases_to_same_legacy_trace476
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) :
    (readLocatedAtHead476 r).map LocatedCapture476.erase = readMarkedCapture r := by
  simp only [readLocatedAtHead476,readMarkedCapture]
  split
  · change ((decode r.head.orig.code).bind _).map LocatedCapture476.erase =
      (decode r.head.orig.code).bind _
    simp only [Option.map_bind]
    congr 1
    funext target
    exact located_capture_erases_all_options476 w.offered [] .actual _ target.val
  · rfl

theorem located_at_head_erases_to_same_legacy_capture476
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) :
    (readLocatedAtHead476 r).map LocatedCapture476.uses =
      (runAtBeforeCapture r).map PinnedCapture.uses := by
  have same := congrArg (Option.map Traced.uses) (located_at_head_erases_to_same_legacy_trace476 r)
  simpa only [Option.map_map,Function.comp_def,LocatedCapture476.erase] using same.trans (erasure_at_the_exact_prechecked_head_returns_the_existing_option r)

theorem located_capture_uses_one_actual_typing_walk_in_every_fit476
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) {whereRead : LocatedCapture476 w.offered}
    (executed : readLocatedAtHead476 r = some whereRead) :
    ∃ rebuilt, (∀ m : Model, FitsFull p.state m →
      GeneralDeclarativeRepeatedActual323.eqAt m.assignment (.variable r.head.orig.capture.lower) rebuilt) ∧
      Walk .actual rebuilt r.head.orig.code whereRead.uses := by
  have old : readMarkedCapture r = some whereRead.erase := by
    rw [←located_at_head_erases_to_same_legacy_trace476 r,executed]
    rfl
  exact every_marked_capture_retains_the_legacy_typing_in_all_original_fits r old

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
