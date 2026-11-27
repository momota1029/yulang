import Yulang.GeneralDeclarativeI65I74AuthenticatedPathSound473

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open LiteralFold471 (SourceGate)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeNestedDecode332 (decode)
open GeneralDeclarativeNestedRun332 (run)
open GeneralDeclarativeNestedIndex332 (ofRows)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeWitnessLiteral349 (eqExpr)

def currentRootedUses (p : FullProblem) (original : GeneralDeclarationPatterns.Pattern)
    (code : Expr) (lower : Nat) (row : Equation) : Option (List Occurrence) := do
  let f := translate (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry
    p.old.state.core.current).constructors
    (GeneralSourceMetadataRows291.interpretation p.old.state.core.current.environment.source.snapshot)
  let old ← f (normalize original)
  if eqExpr old code then
    let target ← decode code
    let view : GeneralDeclarativeHead320.State := ⟨p.state.base.core.current.ordinary.normal,[row]⟩
    let index := ofRows (s := view) [row] (fun _ found => found)
    run index .actual (.variable lower) target.val
  else none

theorem exact_current_source_read_erases_to_its_really_called_capture_computation
    {p g gd w} (a : @FieldOrigin p g gd w) :
    (readTyping a).map SourceTyping.uses =
      currentRootedUses p a.head.orig.original a.head.orig.code a.head.orig.capture.lower a.row := by
  unfold readTyping currentRootedUses
  dsimp only
  split
  · rename_i missing
    simp [missing,bind,Option.bind,Option.map]
  · rename_i legacy lexed
    simp only [lexed,bind,Option.bind]
    split
    · cases t : decode a.head.orig.code with
      | none => rfl
      | some node =>
        dsimp only
        split
        · rename_i failed
          simp [failed,Option.map]
        · rename_i uses found
          simp [found,Option.map]
    · simp [Option.map]

theorem original_capture_execution_cannot_distinguish_erased_physical_author_positions
    {p : FullProblem} {g h : SourceGate p} {gd : CheckedTable p.old.state.core.current}
    {w : FieldOriginWire g} {v : FieldOriginWire h}
    (first : FieldOrigin g gd w) (last : FieldOrigin h gd v)
    (sameWritten : first.head.orig.original = last.head.orig.original)
    (sameCode : first.head.orig.code = last.head.orig.code)
    (samePoint : first.head.orig.capture.lower = last.head.orig.capture.lower)
    (sameRow : first.row = last.row) :
    (readTyping first).map SourceTyping.uses = (readTyping last).map SourceTyping.uses := by
  rw [exact_current_source_read_erases_to_its_really_called_capture_computation,
    exact_current_source_read_erases_to_its_really_called_capture_computation,
    sameWritten,sameCode,samePoint,sameRow]

end Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471
