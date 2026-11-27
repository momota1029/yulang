import Yulang.GeneralDeclarativeI65I74BeforeCaptureEvent475
import Yulang.GeneralDeclarativeI65I74AuthenticatedFieldEvent472

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (translate Expr)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open GeneralDeclarativeOrigins321 (restriction from_source)
open GeneralDeclarativeNestedIndex332 (ofRows)
open GeneralDeclarativeNestedDecode332 (decode)
open GeneralDeclarativeNestedRun332 (run)
open GeneralDeclarativeNestedSound332 (sound)
open GeneralDeclarativeInlineTrace331 (Read realize)
open GeneralDeclarativeTermWalk322 (Occurrence Walk)
open LiteralFold471 (inputSourceOnly)
open ObservationSyntax471 (gateFromAttachedAuthor472 monotone_ordinary_input_trace472)

def offeredInputView (p : FullProblem) (w : BeforeCaptureWire) : GeneralDeclarativeHead320.State :=
  ⟨(rawAt p).normal,w.offered.map StampedRead.row⟩

def oldInputIndex (p : FullProblem) (w : BeforeCaptureWire) :=
  ofRows (s := offeredInputView p w) (offeredInputView p w).equations (fun _ h => h)

def actualLegacyQuery (p : FullProblem) :=
  translate (authoredRegistry p.old.state.core.current).constructors
    (interpretation p.old.state.core.current.environment.source.snapshot)

/-- Existing capture result and its literal original source stamp.
The source/order is read before execution. No allocator is called. -/
structure PinnedCapture {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) where
  uses : List Occurrence
  exactLegacy : actualLegacyQuery p (normalize r.head.orig.original) = some r.head.orig.code
  actualRead : Read (offeredInputView p w) .actual
    (.variable r.head.orig.capture.lower) r.head.orig.code uses

def runAtBeforeCapture {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) : Option (PinnedCapture r) := do
  let orig := r.head.orig
  match legacy : actualLegacyQuery p (normalize orig.original) with
  | none => none
  | some got =>
    if eq : eqExpr got orig.code = true then
      let target ← decode orig.code
      match done : run (oldInputIndex p w) .actual (.variable orig.capture.lower) target.val with
      | none => none
      | some uses =>
        some ⟨uses,legacy.trans (congrArg some ((eq_expr ..).mp eq)),
          target.property ▸ sound (oldInputIndex p w) target.val done⟩
    else none

theorem exact_old_capture_output_after_erasing_checked_stamp {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w)
    (legacy : actualLegacyQuery p (normalize r.head.orig.original) = some r.head.orig.code) :
    (runAtBeforeCapture r).map PinnedCapture.uses =
      (decode r.head.orig.code).bind
        (fun target => run (oldInputIndex p w) .actual (.variable r.head.orig.capture.lower) target.val) := by
  have code : eqExpr r.head.orig.code r.head.orig.code = true := (eq_expr ..).mpr rfl
  unfold runAtBeforeCapture
  dsimp only
  split
  · rename_i missing
    rw [legacy] at missing
    contradiction
  · rename_i got read
    have same := Option.some.inj (read.symm.trans legacy)
    subst got
    simp only [code,dite_true,bind,Option.bind]
    cases d : decode r.head.orig.code with
    | none => rfl
    | some target =>
      dsimp only
      split
      · rename_i missed; rw [missed]; rfl
      · rename_i _ got; exact got.symm

theorem exact_pinned_capture_uses_authored_not_output_only_support {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} (c : PinnedCapture r) :
    Read (restriction (inputSourceOnly (gateFromAttachedAuthor472 (p := p) a))) .actual
      (.variable r.head.orig.capture.lower) r.head.orig.code c.uses := by
  apply monotone_ordinary_input_trace472 (s := offeredInputView p w)
    (t := restriction (inputSourceOnly (gateFromAttachedAuthor472 (p := p) a))) rfl _ c.actualRead
  intro row h
  change row ∈ w.offered.map StampedRead.row at h
  obtain ⟨got,member,rfl⟩ := List.mem_map.mp h
  have authored : t.authored[got.author]? = some got.row :=
    checkedSubsequence_exact.mp (Bool.and_eq_true_iff.mp r.checked).2 _
      (List.mem_map.mpr ⟨got,member,rfl⟩)
  exact from_source _ (List.mem_of_getElem? authored)

theorem one_before_capture_supports_one_walk_in_every_same_fit {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} (c : PinnedCapture r) :
    ∃ rebuilt, (∀ m : Model, FitsFull p.state m →
      GeneralDeclarativeRepeatedActual323.eqAt m.assignment (.variable r.head.orig.capture.lower) rebuilt) ∧
      Walk .actual rebuilt r.head.orig.code c.uses := by
  obtain ⟨term,means,walk⟩ := realize (exact_pinned_capture_uses_authored_not_output_only_support c)
  exact ⟨term,fun m fit => means m.assignment fit.1.1.1,walk⟩

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
