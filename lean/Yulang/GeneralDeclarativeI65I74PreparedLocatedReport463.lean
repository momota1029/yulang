import Yulang.GeneralDeclarativeI65I74PreparedIndexedField463
import Yulang.GeneralDeclarativeI65I74IndexedNativeEvidence463
import Yulang.GeneralDeclarativeI65I74OriginalPhysicalPositions463
import Yulang.GeneralDeclarativeI65I74PreviousStabilityFactorization461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
open EligibleFieldStart461 WrittenPattern460 PhysicalVisit463
open WrittenPattern460.PhysicalOrigin (Hit locateRoute OriginalWalk route_occurrences_exact
  whole_route_is_literal_and_preserves_exact_coordinates atSource)
open RoutedReadyMixed457 (ReportAtField)
open RecordK2412 (checkCycleAt412)
open RoutedMixed456 (endsAtField)
open InlineStructuralPolicy458 (policy)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)

private theorem same_eligible_source_of_one_original_problem
    {p : Checker408.Problem} (a b : EligibleStart p) : a = b :=
  same_eligible_original_anchor_keeps_all_start_data
    (actual_source_anchor_is_determined_by_its_positions_in_same_problem rfl)

structure LocatedReport where
  report : ReportAtField
  mark : Bool
  equations : List Nat
  literal : List Hit

/-- Attach source positions without changing the existing raw report.
A hit list is not a choice of display location. An empty hit list is an
unproved provenance boundary, not a verdict. -/
def readLocated {input : Input} (w : PreparedWire input) : Option LocatedReport := do
  let a ← readPrepared (p := input.problem.old) input.checked w.start
  let (path,n,_,used) ← readJoint input.problem.old.state.core.current.ordinary
    (policy input.problem.old.state.core) (fun _ => queryKeys input.problem.old.state.core)
    inheritedCompilerPlacement a.argument.lower (normalized (readTerm a.original)) a.query w.along.visit
  if endsAtField path n && checkCycleAt412 input.problem.old.state.core.current.ordinary n w.along.cycle
  then some ⟨exactReport a.anchor path n,used,indexedRows w.along.visit,
    locateRoute (fun _ => queryKeys input.problem.old.state.core) a.original a.argument.lower path⟩
  else none

def stripLiteral (l : LocatedReport) : (ReportAtField × Bool) × List Nat :=
  ((l.report,l.mark),l.equations)

theorem removing_literal_receipts_does_not_change_the_original_route
    {input : Input} (w : PreparedWire input) :
    (readLocated w).map stripLiteral = exactReportWithPhysical w := by
  cases ready : readPrepared (p := input.problem.old) input.checked w.start with
  | none =>
    have prior : (preparedReader (p := input.problem.old) input.checked).read w.start = none := ready
    simp [readLocated,exactReportWithPhysical,readSourceAndFieldStamp,ready,prior,Option.bind]
  | some a =>
    have prior : (preparedReader (p := input.problem.old) input.checked).read w.start = some a := ready
    cases route : readJoint input.problem.old.state.core.current.ordinary
        (policy input.problem.old.state.core) (fun _ => queryKeys input.problem.old.state.core)
        inheritedCompilerPlacement a.argument.lower (normalized (readTerm a.original)) a.query w.along.visit with
    | none =>
      simp [readLocated,exactReportWithPhysical,readSourceAndFieldStamp,ready,prior,route,Option.bind]
    | some result =>
      obtain ⟨xs,n,last,used⟩ := result
      by_cases done : endsAtField xs n = true ∧
        checkCycleAt412 input.problem.old.state.core.current.ordinary n w.along.cycle = true <;>
        simp [readLocated,exactReportWithPhysical,readSourceAndFieldStamp,ready,prior,route,done,Option.bind,stripLiteral]

theorem same_read_returns_every_literal_position_of_its_same_original_input
    {input : Input} {w : PreparedWire input} {l : LocatedReport}
    (ok : readLocated w = some l)
    {a : EligibleStart input.problem.old} :
    l.literal = locateRoute (fun _ => queryKeys input.problem.old.state.core)
      a.original a.argument.lower l.report.path := by
  cases header : readPrepared (p := input.problem.old) input.checked w.start with
  | none => simp [readLocated,header,Option.bind] at ok
  | some actual =>
    have x := same_eligible_source_of_one_original_problem actual a
    subst actual
    cases route : readJoint input.problem.old.state.core.current.ordinary
        (policy input.problem.old.state.core) (fun _ => queryKeys input.problem.old.state.core)
        inheritedCompilerPlacement a.argument.lower (normalized (readTerm a.original)) a.query w.along.visit with
    | none => simp [readLocated,header,route,Option.bind] at ok
    | some out =>
      obtain ⟨xs,n,last,stamp⟩ := out
      by_cases done : endsAtField xs n = true ∧
          checkCycleAt412 input.problem.old.state.core.current.ordinary n w.along.cycle = true
      · have eq := Option.some.inj (show some _ = some l from by
          simpa [readLocated,header,route,done,Option.bind] using ok)
        subst l
        rfl
      · simp [readLocated,header,route,done,Option.bind] at ok

def ExactLocated (input : Input) (l : LocatedReport) : Prop :=
  IndependentPhysicalField input l.report l.mark l.equations ∧
    ∃ e : EligibleStart input.problem.old, l.literal =
      locateRoute (fun _ => queryKeys input.problem.old.state.core) e.original e.argument.lower l.report.path

theorem exact_located_report_iff_same_original_finite_wire (input : Input) (l : LocatedReport) :
    ExactLocated input l ↔ ∃ w, readLocated (input := input) w = some l := by
  constructor
  · rintro ⟨physical,a,expected⟩
    obtain ⟨w,checked⟩ := (checked_source_and_actual_indexed_report_iff_finite_witness ..).mp physical
    rw [← removing_literal_receipts_does_not_change_the_original_route w] at checked
    obtain ⟨out,found,same⟩ := Option.map_eq_some_iff.mp checked
    have lit := same_read_returns_every_literal_position_of_its_same_original_input found (a := a)
    have values := Prod.mk.inj same
    have rep := Prod.mk.inj values.1
    have eq : out = l := by
      cases out
      cases l
      dsimp [stripLiteral] at rep values lit expected
      simp_all
    exact ⟨w,eq ▸ found⟩
  · rintro ⟨w,read⟩
    have found : exactReportWithPhysical w = some ((l.report,l.mark),l.equations) := by
      rw [← removing_literal_receipts_does_not_change_the_original_route w,read]
      rfl
    have physical := (checked_source_and_actual_indexed_report_iff_finite_witness ..).mpr ⟨w,found⟩
    obtain ⟨a,_,_,_,_,_,_⟩ := physical
    exact ⟨(checked_source_and_actual_indexed_report_iff_finite_witness ..).mpr ⟨w,found⟩,a,
      same_read_returns_every_literal_position_of_its_same_original_input read⟩

end Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
