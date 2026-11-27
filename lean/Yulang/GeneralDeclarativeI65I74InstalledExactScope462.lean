import Yulang.GeneralDeclarativeI65I74InstalledSameBoolean462

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InstalledProtocolSum462
open EligibleFieldStart461 WrittenPattern460
open Checker408 (Problem)
open RetainedFull445 (FullProblem)
open RoutedReadyMixed457 (ReportAtField)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open RoutedMixed456 (endsAtField)
open InlineStructuralPolicy458 (policy emptyPolicy eraseCycle lift_erase_cycle458)
open RecordK2412 (checkCycleAt412)

def ExactInstalledField (p : Problem) (i : Provider) (r : ReportAtField) : Prop :=
  ∃ (a : EligibleStart p) (last : Term),
    actualHeaderAuthority (provider p i) a ∧
    ScopedRaw p.state.core a.argument.lower (normalized (readTerm a.original))
      a.query r.path r.terminal last true ∧
    endsAtField r.path r.terminal = true ∧
    AliasCycle p.state.core.current.ordinary (observed p.state.core.current.ordinary) r.terminal ∧
    exactReport a.anchor r.path r.terminal = r

/-- Independence resides in the authored judgement and the scoped trace.
The witness is only old data, with the original use stamp retained. -/
theorem exact_installed_scope_iff_finite_witness (p : Problem) (i : Provider) (r : ReportAtField) :
    ExactInstalledField p i r ↔
      ∃ (k : Nat) (w : AuthenticatedHop458.CycleWire emptyPolicy), checkSameField p i k w r = true := by
  constructor
  · rintro ⟨a,last,author,trace,field,cycle,identity⟩
    have authored := anchor_compiles_the_normalized_original a.anchor
    have joint := compiled_trace_has_structural_joint_trace
      (exact_scope_reifies_full_trace_by_descent authored trace)
    have raw := joint_has_actual_raw_trace joint
    obtain ⟨cursor,checked⟩ := (AuthenticatedHop458.exact_used_cycle_has_finite_wire458
      _ _ _ _ _ _).mpr ⟨raw,cycle⟩
    change AuthenticatedHop458.readCycle p.state.core.current.ordinary (policy p.state.core)
      a.argument.lower a.query cursor = some (r.path,r.terminal) at checked
    obtain ⟨k,entered⟩ := (genuine_independent_start_iff_finite_header_ticket _ _).mpr author
    refine ⟨k,eraseCycle p.state.core cursor,(check_same_field_means_same_report ..).mpr ?_⟩
    simp [entered,originalField,lift_erase_cycle458,checked,field,identity,Option.bind]
  · rintro ⟨k,cursor,yes⟩
    have result := (check_same_field_means_same_report ..).mp yes
    obtain ⟨a,admitted,report⟩ := Option.bind_eq_some_iff.mp result
    have author := (genuine_independent_start_iff_finite_header_ticket _ _).mp ⟨k,admitted⟩
    unfold originalField at report
    cases read : AuthenticatedHop458.readCycle p.state.core.current.ordinary (policy p.state.core)
        a.argument.lower a.query (InlineStructuralPolicy458.liftCycle p.state.core cursor) with
    | none => simp [read,Option.bind] at report
    | some out =>
      obtain ⟨path,n⟩ := out
      by_cases field : endsAtField path n = true
      · have identity : exactReport a.anchor path n = r := by
          simpa [read,field,Option.bind] using report
        subst r
        obtain ⟨raw,cycle⟩ := (AuthenticatedHop458.exact_used_cycle_has_finite_wire458
          _ _ _ _ _ _).mp ⟨_,read⟩
        obtain ⟨empty,kind,closed⟩ := all_existing_provider_results_have_original_grammar admitted
        obtain ⟨last,trace⟩ := old_raw_trail_has_authored_scope_without_extra_path_assumptions
          kind closed (anchor_compiles_the_normalized_original a.anchor) raw
        exact ⟨a,last,author,full_trace_reflects_exact_compiled_scope trace,field,cycle,rfl⟩
      · simp [read,field,Option.bind] at report

theorem exact_installed_scope_preserves_authenticated_field_in_every_same_fit
    {p : FullProblem} {i : Provider} {r : ReportAtField} (source : ExactInstalledField p.old i r)
    (m : I72.Model) (fit : I72.FitsFull p.state m) :
    ∃ (a : EligibleStart p.old) (last : Term),
      exactReport a.anchor r.path r.terminal = r ∧
      RoutedInlineStructural458.ModelTrail p.state.base.core m a.argument.lower a.query
        r.path r.terminal true ∧
      CoordinateWalk (fun _ => queryKeys p.state.base.core) a.argument.lower
        (normalized (readTerm a.original)) r.path r.terminal last ∧
      AliasCycle p.state.base.core.current.ordinary
        (observed p.state.base.core.current.ordinary) r.terminal := by
  obtain ⟨a,last,_,scope,field,cycle,report⟩ := source
  have trail := exact_scope_reifies_full_trace_by_descent
    (anchor_compiles_the_normalized_original a.anchor) scope
  have both := compiled_trace_has_structural_joint_trace trail
  have data := RoutedInlineStructural458.used_source_hops_hold_in_the_same_model458
    (joint_has_actual_raw_trace both) m fit.1
  exact ⟨a,last,report,data,joint_has_exact_written_path both,cycle⟩

end Yulang.GeneralDeclarativeI65.I72.InstalledProtocolSum462
