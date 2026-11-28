import Yulang.GeneralDeclarativeI65I74G04ProducerMeaning479

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Producer479
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open GeneralDeclarativeHead320 (Equation)
open NativeProducer465 (CheckedPhase PhaseOriginAt checkPhaseOrigin
  finite_phase_origin_check_iff_literal_placed_active_row)
open InputCoordinates475 (rawAt SamePhaseInputObservation478)

/-- Check a previously entered association at the same physical old row,
then require the actual open release. The association's source is still
the independent completion history, not the ordinary input reader. -/
def readBoundReleasedIssue {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (basis : PriorPhase)
    (phase : CheckedPhase p.old.state.core) (ordinaryOwner : Nat)
    (route : RouteWire n) (data : ReleasedIssueData) :
    Option SamePhaseInputObservation478 := do
  let selected := (pos.cells.get route.trail.cursor.which).oldOrdinal
  let row ← (rawAt p).equations[selected]?
  if (⟨ordinaryOwner,selected,row,data.write,data.originOrdinal⟩ : CompletedAssociation) ∈
      basis.completed then
    readReleasedIssueAtRoute p gd pos rel phase route data
  else none

theorem exact_output_association_and_current_release_replay479
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel} {basis : PriorPhase} {phase : CheckedPhase p.old.state.core} {ordinaryOwner route data out} :
    readBoundReleasedIssue p gd pos rel basis phase ordinaryOwner route data = some out ↔
      ∃ row : Equation,
        (rawAt p).equations[(pos.cells.get route.trail.cursor.which).oldOrdinal]? = some row ∧
        (⟨ordinaryOwner,(pos.cells.get route.trail.cursor.which).oldOrdinal,row,
          data.write,data.originOrdinal⟩ : CompletedAssociation) ∈ basis.completed ∧
        PhaseOriginAt phase data.write row.left data.originOrdinal ∧
        readRoute p gd pos rel route = some out := by
  let selected := (pos.cells.get route.trail.cursor.which).oldOrdinal
  constructor
  · intro ran
    cases found : (rawAt p).equations[selected]? with
    | none => simp [readBoundReleasedIssue,selected,found] at ran
    | some row =>
      have run : (if (⟨ordinaryOwner,selected,row,data.write,data.originOrdinal⟩ :
          CompletedAssociation) ∈ basis.completed then
          readReleasedIssueAtRoute p gd pos rel phase route data else none) = some out := by
        simpa [readBoundReleasedIssue,selected,found,bind,Option.bind] using ran
      split at run
      · rename_i member
        have exactCheck : (if checkPhaseOrigin phase data.write row.left data.originOrdinal then
            readRoute p gd pos rel route else none) = some out := by
          simpa [readReleasedIssueAtRoute,checkReleasedRoot,selected,found] using run
        split at exactCheck
        · rename_i yes
          exact ⟨row,rfl,member,
            (finite_phase_origin_check_iff_literal_placed_active_row ..).mp yes,exactCheck⟩
        · cases exactCheck
      · cases run
  · rintro ⟨row,found,seen,active,checked⟩
    simp [readBoundReleasedIssue,readReleasedIssueAtRoute,checkReleasedRoot,found,seen,
      (finite_phase_origin_check_iff_literal_placed_active_row ..).mpr active,checked,bind,Option.bind]

end Yulang.GeneralDeclarativeI65.I72.Producer479
