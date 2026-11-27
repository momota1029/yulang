import Yulang.GeneralDeclarativeI65I74InstalledProtocolSum462

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InstalledProtocolSum462
open EligibleFieldStart461 WrittenPattern460
open Checker408 (Problem)
open RoutedReadyMixed457 (ReportAtField)
open RoutedMixed456 (endsAtField)
open InlineStructuralPolicy458 (policy liftCycle emptyPolicy)
open RecordK2412 (checkCycleAt412)

def onOldCursor (p : Problem) (i : Provider) (k : Nat)
    (w : AuthenticatedHop458.CycleWire emptyPolicy) : InstalledWire p :=
  let lifted := liftCycle p.state.core w
  ⟨⟨i,k⟩,⟨addUnitPlacement lifted.trail,lifted.cycle⟩⟩

def originalField {p : Problem} (a : EligibleStart p)
    (w : AuthenticatedHop458.CycleWire emptyPolicy) : Option ReportAtField := do
  let (path,n) ← AuthenticatedHop458.readCycle p.state.core.current.ordinary
    (policy p.state.core) a.argument.lower a.query (liftCycle p.state.core w)
  if endsAtField path n then return exactReport a.anchor path n else none

/-- This is a property of a genuine provider result, not a witness field. -/
def SourceGrammar {p : Problem} (a : EligibleStart p) : Prop :=
  ∃ k, queryKeys p.state.core k = .emptyRow ∧
    ActualClosedSyntax p.state.core k (normalized (readTerm a.original))

private theorem old_raw_success_has_same_written_coordinates {p : Problem} {a : EligibleStart p}
    (gram : SourceGrammar a) {w : AuthenticatedHop458.Wire (policy p.state.core)}
    {path n used}
    (raw : AuthenticatedHop458.readTrail p.state.core.current.ordinary (policy p.state.core)
      a.argument.lower a.query w = some (path,n,used)) :
    ∃ last, readCoordinates (fun _ => queryKeys p.state.core) a.argument.lower
      (normalized (readTerm a.original)) path = some last := by
  obtain ⟨k,empty,form⟩ := gram
  obtain ⟨last,result⟩ := old_raw_trail_has_authored_scope_without_extra_path_assumptions
    empty form (anchor_compiles_the_normalized_original a.anchor)
    (AuthenticatedHop458.read_trail_sound458 raw)
  have written := (authored_trail_normal_form.mp result).2.2
  exact ⟨last,(selected_coordinates_iff_independent_walk
    (coordinate_walk_last_original_cell written)).mpr written⟩

private theorem stamped_eq_iff_same_original_raw_read {p : Problem} (a : EligibleStart p)
    (gram : SourceGrammar a) (w : AuthenticatedHop458.CycleWire emptyPolicy)
    (r : ReportAtField) :
    ((do
      let (path,n,_,used) ← readJoint p.state.core.current.ordinary (policy p.state.core)
        (fun _ => queryKeys p.state.core) inheritedCompilerPlacement a.argument.lower
        (normalized (readTerm a.original)) a.query
        (addUnitPlacement (liftCycle p.state.core w).trail)
      if endsAtField path n && checkCycleAt412 p.state.core.current.ordinary n
        (liftCycle p.state.core w).cycle
      then some (exactReport a.anchor path n,used) else none) = some (r,true)) ↔
      originalField a w = some r := by
  rw [interleaved_read_factors_through_the_identical_raw_run]
  unfold originalField AuthenticatedHop458.readCycle
  cases raw : AuthenticatedHop458.readTrail p.state.core.current.ordinary (policy p.state.core)
      a.argument.lower a.query (liftCycle p.state.core w).trail with
  | none => simp [Option.bind]
  | some run =>
    obtain ⟨path,n,used⟩ := run
    obtain ⟨last,coords⟩ := old_raw_success_has_same_written_coordinates gram raw
    cases used <;> cases field : endsAtField path n <;>
      cases cycle : checkCycleAt412 p.state.core.current.ordinary n (liftCycle p.state.core w).cycle <;>
      simp [coords,field,cycle,Option.bind]

theorem uniform_reader_on_same_data_matches_original_raw_report
    (p : Problem) (i : Provider) (k : Nat) (w : AuthenticatedHop458.CycleWire emptyPolicy)
    (gram : ∀ a, readActualHeader (provider p i) k = some a → SourceGrammar a)
    (r : ReportAtField) :
    dispatchReport (onOldCursor p i k w) = some (r,true) ↔
      ((readActualHeader (provider p i) k).bind fun a => originalField a w) = some r := by
  cases got : readActualHeader (provider p i) k with
  | none =>
    have no : (installedRead p).read (⟨i,k⟩ : Ticket) = none := got
    simp [dispatchReport,onOldCursor,readSourceAndFieldStamp,no,Option.bind]
  | some a =>
    have yes : (installedRead p).read (⟨i,k⟩ : Ticket) = some a := got
    change ((installedRead p).read ⟨i,k⟩).bind _ = _ ↔ _
    rw [yes]
    exact stamped_eq_iff_same_original_raw_read a (gram a got) w r

end Yulang.GeneralDeclarativeI65.I72.InstalledProtocolSum462
