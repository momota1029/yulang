import Yulang.GeneralDeclarativeI65I74SameBooleanFieldStamp461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
open WrittenPattern460
open Checker408 (Problem)
open RetainedFull445 (FullProblem)
open RoutedReadyMixed457 (ReportAtField)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open RecordTraversal455 (naked_raw_cycle_has_finite_wire455)
open RecordK2412 (checkCycleAt412 cycle_at_sound412)
open InlineStructuralPolicy458 (policy)
open RoutedMixed456 (endsAtField)

def ExactStampedSource {p : Problem} (provider : ReadyRead p) (r : ReportAtField)
    (used : Bool) : Prop :=
  ∃ (a : EligibleStart p) (last : Term), provider.authority a ∧
    ScopedRaw p.state.core a.argument.lower (normalized (readTerm a.original))
      a.query r.path r.terminal last used ∧
    endsAtField r.path r.terminal = true ∧
    AliasCycle p.state.core.current.ordinary (observed p.state.core.current.ordinary) r.terminal ∧
    exactReport a.anchor r.path r.terminal = r

theorem stamped_source_iff_exact_finite_structural_read {p : Problem}
    (provider : ReadyRead p) (r : ReportAtField) (used : Bool) :
    ExactStampedSource provider r used ↔
      ∃ w, readSourceAndFieldStamp provider w = some (r,used) := by
  constructor
  · rintro ⟨a,last,source,path,field,cycle,identity⟩
    obtain ⟨key,header⟩ := (provider.exact a).mpr source
    have compiled := exact_scope_reifies_full_trace_by_descent
      (anchor_compiles_the_normalized_original a.anchor) path
    obtain ⟨cursor,walk⟩ := joint_wire_complete (compiled_trace_has_structural_joint_trace compiled)
    obtain ⟨k2,k⟩ := (naked_raw_cycle_has_finite_wire455 p.state.core.current.ordinary r.terminal).mp cycle
    refine ⟨⟨key,⟨cursor,k2⟩⟩,?_⟩
    change readJoint p.state.core.current.ordinary (policy p.state.core) (fun _ => queryKeys p.state.core)
      inheritedCompilerPlacement a.argument.lower (normalized (readTerm a.original)) a.query cursor =
        some (r.path,r.terminal,last,used) at walk
    simp [readSourceAndFieldStamp,header,walk,field,k,identity,Option.bind]
  · rintro ⟨w,yes⟩
    cases header : provider.read w.start with
    | none => simp [readSourceAndFieldStamp,header,Option.bind] at yes
    | some a =>
      cases walk : readJoint p.state.core.current.ordinary (policy p.state.core)
          (fun _ => queryKeys p.state.core) inheritedCompilerPlacement a.argument.lower
          (normalized (readTerm a.original)) a.query w.along.visit with
      | none => simp [readSourceAndFieldStamp,header,walk,Option.bind] at yes
      | some out =>
        obtain ⟨steps,n,last,stamp⟩ := out
        by_cases final : endsAtField steps n = true ∧
            checkCycleAt412 p.state.core.current.ordinary n w.along.cycle = true
        · have report : exactReport a.anchor steps n = r ∧ stamp = used := by
            simpa [readSourceAndFieldStamp,header,walk,final,Option.bind] using yes
          obtain ⟨rfl,rfl⟩ := report
          have compiled := descend_actual_compiler_alignment
            (anchor_compiles_the_normalized_original a.anchor) (read_joint_sound walk)
          exact ⟨a,last,(provider.exact a).mp ⟨w.start,header⟩,
            full_trace_reflects_exact_compiled_scope compiled,final.1,cycle_at_sound412 final.2,rfl⟩
        · simp [readSourceAndFieldStamp,header,walk,final,Option.bind] at yes

theorem stamped_scope_has_exact_source_route_and_same_model_evidence
    {p : FullProblem} {provider : ReadyRead p.old} {r : ReportAtField} {used : Bool}
    (source : ExactStampedSource provider r used) (m : I72.Model) (fit : I72.FitsFull p.state m) :
    ∃ (a : EligibleStart p.old) (last : Term), provider.authority a ∧
      exactReport a.anchor r.path r.terminal = r ∧
      RoutedInlineStructural458.ModelTrail p.state.base.core m a.argument.lower a.query
        r.path r.terminal used ∧
      CoordinateWalk (fun _ => queryKeys p.state.base.core) a.argument.lower
        (normalized (readTerm a.original)) r.path r.terminal last ∧
      AliasCycle p.state.base.core.current.ordinary
        (observed p.state.base.core.current.ordinary) r.terminal := by
  obtain ⟨a,last,source,path,_,cycle,identity⟩ := source
  have joint := compiled_trace_has_structural_joint_trace
    (exact_scope_reifies_full_trace_by_descent (anchor_compiles_the_normalized_original a.anchor) path)
  exact ⟨a,last,source,identity,
    RoutedInlineStructural458.used_source_hops_hold_in_the_same_model458
      (joint_has_actual_raw_trace joint) m fit.1,joint_has_exact_written_path joint,cycle⟩

end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
