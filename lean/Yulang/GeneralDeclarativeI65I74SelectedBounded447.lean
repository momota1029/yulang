import Yulang.GeneralDeclarativeI65I74SelectedExact447
import Yulang.GeneralDeclarativeI65I74SplitCompact447

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RetainedSplit446.SelectedReplay447
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem)
open RetainedFull445
open RetainedFull445.PlacementQA (canonical_placement_keeps_same_original_report445)
open MixedFixed442
open SplitEscape446
open SplitEscape446.SplitCompact447

/-- Bounded table count for the exact report of the original selected
local event. N is the largest raw name plus one at the original site
(or an equivalent finite cap), not the number of distinct graph nodes.
This is existence of finite data, not executable witness synthesis. -/
theorem independent_selected_report_has_compact_witness447 (p : FullProblem)
    (a : LocalSelection p.state p.root) :
    ∃ w : RefPositions441.Wire,
      check_full447 p a.report (.localSplitOutput w) = true ∧
      w.escape.ranks.length = rawLimit p.state.base.core.current.ordinary
        a.source.origin.original.arg.lower ∧
      w.escape.palette.length = rawLimit p.state.base.core.current.ordinary
        a.source.origin.original.arg.lower + 1 := by
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
  let input := n.origin.original
  have siteSame : input.arg.lower = a.source.origin.original.arg.lower := by
    have loc : input.arg = a.source.origin.original.arg :=
      List.singleton_inj.mp (input.asked.symm.trans a.source.origin.original.asked)
    exact congrArg (·.lower) loc
  obtain ⟨table,checked,grades,palette⟩ := (raw_safe_iff_small_witness447
    p.state.base.core.current.ordinary input.arg.lower).mp (original_selected_site_is_raw_safe446 n)
  obtain ⟨position,found⟩ := List.mem_iff_getElem?.mp input.authored
  let w : RefPositions441.Wire := ⟨position,table⟩
  have sound := exact_source_read_reifies_split_safe_witness446 p chosen w
    (ready_local_exact_read n w found checked place)
  have exactReport : chosen.report = a.report := report
  exact ⟨w,exactReport ▸ sound,grades.trans (congrArg (rawLimit p.state.base.core.current.ordinary) siteSame),
    palette.trans (congrArg (fun n => rawLimit p.state.base.core.current.ordinary n + 1) siteSame)⟩

end Yulang.GeneralDeclarativeI65.I72.RetainedSplit446.SelectedReplay447
