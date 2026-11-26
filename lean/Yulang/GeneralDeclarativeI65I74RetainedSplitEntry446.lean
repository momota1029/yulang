import Yulang.GeneralDeclarativeI65I74RetainedSplitReader446

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RetainedSplit446
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem Result)
open RetainedFull445
open RetainedFull445.PlacementQA (canonical_placement_keeps_same_original_report445)
open SplitEscape446
open MixedFixed442
open WhereAssociated432 (matchesAssociatedReport432 matches_associated_report_exact432)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)

/-- The new case adds only a data witness for the same original
selected report. Every pre-existing witness takes the exact old
entry, not a converted or reinterpreted check. -/
inductive Witness446 where
  | previous (w : RetainedFull445.Witness)
  | splitOutput (input : RefPositions441.Wire)

def check_full446 (p : FullProblem) (r : Result) : Witness446 → Bool
  | .previous w => RetainedFull445.check_full p r w
  | .splitOutput w =>
    match readSource446 p.old w with
    | none => false
    | some source => matchesSelection p source && matchesAssociatedReport432 r (sourceReport source)

theorem all_C445_Bool_unchanged446 (p : FullProblem) (r : Result)
    (w : RetainedFull445.Witness) :
    check_full446 p r (.previous w) = RetainedFull445.check_full p r w := rfl

theorem all_R21_Bool_unchanged446 (p : Problem) (r : Result) (w : RefPositions441.Witness) :
    check_full446 (liftProblem p) r (.previous (.previous w)) = RefPositions441.check p r w :=
  all_R21_Bool_unchanged_on_lift445 p r w

theorem check_full_sound446 (p : FullProblem) (r : Result) (w : Witness446)
    (yes : check_full446 p r w = true) :
    ClassifiedAsFull p.state p.root r ∧
      ∀ m : I72.Model, FitsFull p.state m → ReportEvidenceFull p.state m p.root r := by
  cases w with
  | previous old => exact RetainedFull445.check_full_sound p r old yes
  | splitOutput wire =>
    simp only [check_full446] at yes
    cases got : readSource446 p.old wire with
    | none => simp [got] at yes
    | some source =>
      rw [got] at yes
      obtain ⟨matched,reported⟩ := Bool.and_eq_true_iff.mp yes
      obtain ⟨a,same⟩ := matches_selection_exact445 matched
      have report : r = a.report := by
        change r = sourceReport a.source
        rw [same]
        exact (matches_associated_report_exact432 _ _).mp reported
      refine ⟨.inr ⟨a,report⟩,fun m fit => ?_⟩
      have exactTargets := stored_selection_fixed_targets445 a.kept m fit
      exact .inr ⟨a,report,source_event_dictionary445 a.source m fit.1 exactTargets,exactTargets⟩

theorem exact_source_read_reifies_split_safe_witness446 (p : FullProblem)
    (a : LocalSelection p.state p.root)
    (w : RefPositions441.Wire) (read : readSource446 p.old w = some a.source) :
    check_full446 p a.report (.splitOutput w) = true := by
  simp only [check_full446,read]
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_,(matches_associated_report_exact432 _ _).mpr rfl⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨(check_fresh_exact445 _).mpr a.fresh,?_⟩
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true a.single,stored_selection_matches445 a.kept⟩

/-- Raw safety is already part of the independently selected original
input proof. No executable result, external rank certificate or
invented winner condition is a premise. -/
theorem original_selected_site_is_raw_safe446 {p : Problem} (source : SourceSelection p) :
    ¬AliasCycle p.state.core.current.ordinary (observed p.state.core.current.ordinary)
      source.origin.original.arg.lower := by
  intro cycle
  apply source.origin.original.safe
  refine ⟨source.origin.original.arg,?_,cycle⟩
  rw [source.origin.original.asked]
  exact List.mem_cons_self

theorem canonical_local_has_split_witness446 (p : FullProblem)
    (a : LocalSelection p.state p.root)
    (header : HeaderReady445 p.state.base.core.current.environment)
    (place : a.source.origin.event.frame.placement = unusedPlacement403) :
    ∃ w : RefPositions441.Wire, check_full446 p a.report (.splitOutput w) = true := by
  let input := a.source.origin.original
  obtain ⟨table,safe⟩ := (raw_safe_iff_finite_split_witness446 p.state.base.core.current.ordinary
    input.arg.lower).mp (original_selected_site_is_raw_safe446 a.source)
  obtain ⟨position,found⟩ := List.mem_iff_getElem?.mp input.authored
  let w : RefPositions441.Wire := ⟨position,table⟩
  exact ⟨w,exact_source_read_reifies_split_safe_witness446 p a w
    (ready_split_exact_read446 a.source w (ready_header_check445 header) found safe place)⟩

/-- Global header readiness is now the only additional premise in
this scoped concretization theorem. The exact pre-existing report,
including output order and addresses, is preserved. -/
theorem independent_local_and_header_have_exact_witness446 (p : FullProblem)
    (a : LocalSelection p.state p.root)
    (header : HeaderReady445 p.state.base.core.current.environment) :
    ∃ w : RefPositions441.Wire, check_full446 p a.report (.splitOutput w) = true := by
  obtain ⟨n,place,_,_,cap,key,report⟩ := canonical_placement_keeps_same_original_report445 a.source
  have indexOf (source : SourceSelection p.old) : source.origin.i0.val = 0 := rfl
  have compare : n.origin.i0 = a.source.origin.i0 := Fin.ext
    ((indexOf n).trans (indexOf a.source).symm)
  let atTarget (i : Fin p.root.demand.outputs.length) : Nat := p.root.demand.outputs[i].target
  have sameTarget := congrArg atTarget compare
  have fresh : FreshOutput n := by
    change atTarget n.origin.i0 ∉ oldReadNames p.state.base.core ∧
      n.own.2.out.valueCap.center ≠ atTarget n.origin.i0
    rw [sameTarget,cap]
    exact a.fresh
  let kept : StoredSelection p.state n :=
    ⟨a.kept.row,a.kept.member,a.kept.shape,a.kept.exactKey.trans key.symm⟩
  let chosen : LocalSelection p.state p.root := ⟨n,fresh,kept,a.single⟩
  obtain ⟨w,sound⟩ := canonical_local_has_split_witness446 p chosen header place
  have exactReport : chosen.report = a.report := report
  exact ⟨w,exactReport ▸ sound⟩

end Yulang.GeneralDeclarativeI65.I72.RetainedSplit446
