import Yulang.GeneralDeclarativeI65I74MarkedCaptureErasure475

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeNestedDecode332 (decode)
open GeneralDeclarativeNestedRun332 (run)
open GeneralDeclarativeTermWalk322 (Walk)

def legacyCodeMatches (p : FullProblem)
    (head : PreparedDeclarations463.OriginalHead p.old) : Bool :=
  (actualLegacyQuery p (normalize head.original)).any
    (fun got => GeneralDeclarativeWitnessLiteral349.eqExpr got head.code)

theorem legacy_code_matches_exact (p : FullProblem)
    (head : PreparedDeclarations463.OriginalHead p.old) :
    legacyCodeMatches p head = true ↔ actualLegacyQuery p (normalize head.original) = some head.code := by
  unfold legacyCodeMatches
  cases seen : actualLegacyQuery p (normalize head.original) with
  | none => simp
  | some got => simp [GeneralDeclarativeWitnessLiteral349.eq_expr]

/-- A capture-local read on the already-checked source view. This
retains each actual name exposure in legacy order, not an origin
for an unresolved input or an origin selected by its model value. -/
def readMarkedCapture {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) : Option (Traced w.offered) :=
  if legacyCodeMatches p r.head.orig then do
    let target ← decode r.head.orig.code
    runMarked w.offered .actual (.variable r.head.orig.capture.lower) target.val
  else none

theorem no_legacy_code_match_returns_no_capture {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} (r : BeforeCapture a gd w)
    (mismatch : actualLegacyQuery p (normalize r.head.orig.original) ≠ some r.head.orig.code) :
    runAtBeforeCapture r = none := by
  unfold runAtBeforeCapture
  dsimp only
  split
  · rfl
  · rename_i got yes
    have test : GeneralDeclarativeWitnessLiteral349.eqExpr got r.head.orig.code ≠ true := by
      intro eq
      exact mismatch (yes.trans (congrArg some ((GeneralDeclarativeWitnessLiteral349.eq_expr ..).mp eq)))
    simp [test]

theorem erasure_at_the_exact_prechecked_head_returns_the_existing_option
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) :
    (readMarkedCapture r).map Traced.uses = (runAtBeforeCapture r).map PinnedCapture.uses := by
  by_cases exact : actualLegacyQuery p (normalize r.head.orig.original) = some r.head.orig.code
  · rw [exact_old_capture_output_after_erasing_checked_stamp r exact]
    have legacy : legacyCodeMatches p r.head.orig = true := (legacy_code_matches_exact ..).mpr exact
    simp only [readMarkedCapture,legacy,ite_true]
    change ((decode r.head.orig.code).bind _).map Traced.uses = (decode r.head.orig.code).bind _
    simp only [Option.map_bind]
    congr 1
    funext target
    exact marked_run_erases (rawAt p) w.offered .actual (.variable r.head.orig.capture.lower) target.val
  · have bad : legacyCodeMatches p r.head.orig ≠ true := fun h => exact ((legacy_code_matches_exact ..).mp h)
    simp [readMarkedCapture,bad,no_legacy_code_match_returns_no_capture r exact]

theorem a_marked_name_exposure_keeps_both_exact_original_rows {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} (r : BeforeCapture a gd w) (event : Opened w.offered) :
    (rawAt p).equations[event.picked.raw]? = some event.picked.row ∧
    t.authored[event.picked.author]? = some event.picked.row ∧
    event.picked.row.left = event.name :=
  first_uses_two_actual_coordinates _ _ _ r.checked event.literalFirst

theorem every_marked_capture_retains_the_legacy_typing_in_all_original_fits
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) {result : Traced w.offered}
    (answered : readMarkedCapture r = some result) :
    ∃ rebuilt, (∀ m : Model, FitsFull p.state m →
      GeneralDeclarativeRepeatedActual323.eqAt m.assignment (.variable r.head.orig.capture.lower) rebuilt) ∧
      Walk .actual rebuilt r.head.orig.code result.uses := by
  have same := erasure_at_the_exact_prechecked_head_returns_the_existing_option r
  rw [answered] at same
  cases m : runAtBeforeCapture r with
  | none => simp [m] at same
  | some original =>
    have sameUses : result.uses = original.uses := by simpa [m] using same
    rw [sameUses]
    exact one_before_capture_supports_one_walk_in_every_same_fit original

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
