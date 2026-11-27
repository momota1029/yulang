import Yulang.GeneralDeclarativeI65I74PreparedOriginalStart463
import Yulang.GeneralDeclarativeI65I74IndexedStructuralTrail463

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
open EligibleFieldStart461 WrittenPattern460 PhysicalVisit463
open Checker408 (Problem)
open RetainedFull445 (FullProblem)
open RoutedReadyMixed457 (ReportAtField)
open InlineStructuralPolicy458 (policy)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open RecordTraversal455 (naked_raw_cycle_has_finite_wire455)
open RecordK2412 (checkCycleAt412 cycle_at_sound412)
open RoutedMixed456 (endsAtField)

abbrev PreparedWire (input : Input) := EligibleWire (preparedReader (p := input.problem.old) input.checked)

def exactReportWithPhysical {input : Input} (w : PreparedWire input) :
    Option ((ReportAtField × Bool) × List Nat) :=
  (readSourceAndFieldStamp (preparedReader (p := input.problem.old) input.checked) w).map
    fun out => (out,indexedRows w.along.visit)

def IndependentPhysicalField (input : Input) (r : ReportAtField) (stamp : Bool) (rows : List Nat) : Prop :=
  let p := input.problem.old
  ∃ (a : EligibleStart p) (last : Term), PreparedSource input.checked a ∧
    IndexedJoint p.state.core.current.ordinary (policy p.state.core) (fun _ => queryKeys p.state.core)
      a.argument.lower (normalized (readTerm a.original)) a.query r.path rows r.terminal last stamp ∧
    endsAtField r.path r.terminal = true ∧
    AliasCycle p.state.core.current.ordinary (observed p.state.core.current.ordinary) r.terminal ∧
    exactReport a.anchor r.path r.terminal = r

theorem checked_source_and_actual_indexed_report_iff_finite_witness
    (input : Input) (r : ReportAtField) (stamp : Bool) (rows : List Nat) :
    IndependentPhysicalField input r stamp rows ↔
      ∃ w, exactReportWithPhysical (input := input) w = some ((r,stamp),rows) := by
  constructor
  · rintro ⟨a,last,author,trail,field,cycle,eq⟩
    obtain ⟨key,ready⟩ := (prepared_source_iff_exact_finite_original_address ..).mpr author
    obtain ⟨w,anchors,atTrail⟩ := exact_indexed_structural_route_has_same_order_finite_wire trail
    obtain ⟨cyc,cy⟩ := (naked_raw_cycle_has_finite_wire455 _ r.terminal).mp cycle
    refine ⟨⟨key,⟨w,cyc⟩⟩,?_⟩
    change readJoint _ _ _ inheritedCompilerPlacement a.argument.lower
      (normalized (readTerm a.original)) a.query w = some (r.path,r.terminal,last,stamp) at atTrail
    have rootRead : (preparedReader (p := input.problem.old) input.checked).read key = some a := ready
    simp [exactReportWithPhysical,readSourceAndFieldStamp,rootRead,atTrail,field,cy,eq,anchors,Option.bind]
  · rintro ⟨w,got⟩
    obtain ⟨⟨result,used⟩,read,eq⟩ := Option.map_eq_some_iff.mp got
    obtain ⟨aEq,bEq⟩ := Prod.mk.inj eq
    obtain ⟨rfl,rfl⟩ := aEq
    subst rows
    cases header : (preparedReader (p := input.problem.old) input.checked).read w.start with
    | none => simp [readSourceAndFieldStamp,header,Option.bind] at read
    | some a =>
      cases scan : readJoint input.problem.old.state.core.current.ordinary
          (policy input.problem.old.state.core) (fun _ => queryKeys input.problem.old.state.core)
          inheritedCompilerPlacement a.argument.lower
          (normalized (readTerm a.original)) a.query w.along.visit with
      | none => simp [readSourceAndFieldStamp,header,scan,Option.bind] at read
      | some out =>
        obtain ⟨path,n,last,used⟩ := out
        by_cases ends : endsAtField path n = true ∧
            checkCycleAt412 input.problem.old.state.core.current.ordinary n w.along.cycle = true
        · have wanted : exactReport a.anchor path n = r ∧ used = stamp := by
            simpa [readSourceAndFieldStamp,header,scan,ends,Option.bind] using read
          obtain ⟨rfl,rfl⟩ := wanted
          exact ⟨a,last,(prepared_source_iff_exact_finite_original_address ..).mp ⟨w.start,header⟩,
            read_same_wire_preserves_every_selected_physical_index scan,ends.1,cycle_at_sound412 ends.2,rfl⟩
        · simp [readSourceAndFieldStamp,header,scan,ends,Option.bind] at read

theorem actual_prepared_physical_route_is_same_original_and_same_fit
    {input : Input} {r : ReportAtField} {stamp : Bool} {rows : List Nat}
    (route : IndependentPhysicalField input r stamp rows)
    (m : I72.Model) (fit : I72.FitsFull input.problem.state m) :
    ∃ (a : EligibleStart input.problem.old) (last : Term), PreparedSource input.checked a ∧
      exactReport a.anchor r.path r.terminal = r ∧
      RoutedInlineStructural458.ModelTrail input.problem.state.base.core m a.argument.lower a.query
        r.path r.terminal stamp ∧
      CoordinateWalk (fun _ => queryKeys input.problem.state.base.core) a.argument.lower
        (normalized (readTerm a.original)) r.path r.terminal last ∧
      AliasCycle input.problem.state.base.core.current.ordinary
        (observed input.problem.state.base.core.current.ordinary) r.terminal := by
  obtain ⟨a,last,auth,trail,_,cycle,eq⟩ := route
  have joint := erase_indices_preserves_an_identical_authorized_trail trail
  exact ⟨a,last,auth,eq,RoutedInlineStructural458.used_source_hops_hold_in_the_same_model458
    (joint_has_actual_raw_trace joint) m fit.1,joint_has_exact_written_path joint,cycle⟩

end Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
