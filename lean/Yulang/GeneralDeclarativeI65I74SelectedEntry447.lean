import Yulang.GeneralDeclarativeI65I74SelectedReflect447

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RetainedSplit446.SelectedReplay447
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
inductive Witness447 where
  | previous (w : RetainedSplit446.Witness446)
  | localSplitOutput (input : RefPositions441.Wire)

def check_full447 (p : FullProblem) (r : Result) : Witness447 → Bool
  | .previous w => RetainedSplit446.check_full446 p r w
  | .localSplitOutput w =>
    match readLocalSource p.old w with
    | none => false
    | some source => matchesSelection p source && matchesAssociatedReport432 r (sourceReport source)

theorem all_published_Bool_unchanged (p : FullProblem) (r : Result)
    (w : RetainedSplit446.Witness446) :
    check_full447 p r (.previous w) = RetainedSplit446.check_full446 p r w := rfl

theorem check_full_sound447 (p : FullProblem) (r : Result) (w : Witness447)
    (yes : check_full447 p r w = true) :
    ClassifiedAsFull p.state p.root r ∧
      ∀ m : I72.Model, FitsFull p.state m → ReportEvidenceFull p.state m p.root r := by
  cases w with
  | previous old => exact RetainedSplit446.check_full_sound446 p r old yes
  | localSplitOutput wire =>
    simp only [check_full447] at yes
    cases got : readLocalSource p.old wire with
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
    (w : RefPositions441.Wire) (read : readLocalSource p.old w = some a.source) :
    check_full447 p a.report (.localSplitOutput w) = true := by
  simp only [check_full447,read]
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
    (place : a.source.origin.event.frame.placement = unusedPlacement403) :
    ∃ w : RefPositions441.Wire, check_full447 p a.report (.localSplitOutput w) = true := by
  let input := a.source.origin.original
  obtain ⟨table,safe⟩ := (raw_safe_iff_finite_split_witness446 p.state.base.core.current.ordinary
    input.arg.lower).mp (original_selected_site_is_raw_safe446 a.source)
  obtain ⟨position,found⟩ := List.mem_iff_getElem?.mp input.authored
  let w : RefPositions441.Wire := ⟨position,table⟩
  exact ⟨w,exact_source_read_reifies_split_safe_witness446 p a w
    (ready_local_exact_read a.source w found safe place)⟩

/-- The checked local rule produces a finite data witness for its exact original report, without an additional global header, escape or placement assumption. -/
theorem independent_selected_report_has_finite_witness447 (p : FullProblem)
    (a : LocalSelection p.state p.root) :
    ∃ w : RefPositions441.Wire, check_full447 p a.report (.localSplitOutput w) = true := by
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
  obtain ⟨w,sound⟩ := canonical_local_has_split_witness446 p chosen place
  have exactReport : chosen.report = a.report := report
  exact ⟨w,exactReport ▸ sound⟩

end Yulang.GeneralDeclarativeI65.I72.RetainedSplit446.SelectedReplay447
