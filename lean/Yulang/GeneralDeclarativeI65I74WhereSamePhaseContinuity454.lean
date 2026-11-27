import Yulang.GeneralDeclarativeI65I74WhereSamePhaseSource454

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.SamePhase454
open Yulang.GeneralDeclarativeI65
open RetainedFull445
open InternalK2452
open LiteralAndInternal452
open GroupedEntry453 (GroupedReport SameReport matchesReport)
open CommonRoleOutermostResolver (Tree)
open GeneralDeclarativeWitnessDeclaredState357 (point)

theorem cyclic_group_nonempty_iff_has_actual_cyclic_child454
    {p : FullProblem} (x : InternalReport p) :
    x.groups ≠ [] ↔ ∃ q ∈ x.original.parent.children, RootCycle p.state.base q := by
  constructor
  · intro someGroup
    obtain ⟨g,rest,seen⟩ := List.exists_cons_of_ne_nil someGroup
    have actual : g ∈ x.groups := seen.symm ▸ List.mem_cons_self
    have facts := one_checked_entry_means_K2_at_every_original452 x.original.diagnostics actual
    obtain ⟨m,ms,first⟩ := List.exists_cons_of_ne_nil facts.2.1
    have mIn : m ∈ g.marks := first.symm ▸ List.mem_cons_self
    have exactly := any_mark_is_actual_original_diagnostic451 x.original.diagnostics
      (facts.2.2.1.subset mIn)
    exact ⟨m.request,List.mem_of_getElem? exactly.1,facts.2.2.2 m mIn⟩
  · rintro ⟨q,inChild,cy⟩ empty
    obtain ⟨i,child⟩ := List.mem_iff_getElem?.mp inChild
    have len : x.original.parent.children.length = x.original.parent.decl.requirements.length := by
      simp [ParentSelection.children,GeneralDeclarativeI65.children]
    have inside : i < x.original.parent.decl.requirements.length :=
      len ▸ (List.getElem?_eq_some_iff.mp child).choose
    let clause := x.original.parent.decl.requirements[i]
    have present : x.original.parent.decl.requirements[i]? = some clause :=
      List.getElem?_eq_getElem inside
    obtain ⟨_,n,l,b,_,_,pos,_⟩ := every_actual_clause_has_a_preserved_location_mark451
      x.original.diagnostics present
    let named : I72.Request := ⟨p.root.occurrence ++ [i],⟨clause.role,[point n],[]⟩⟩
    let m : OriginalMark := ⟨i,clause.id,named,n,l,b⟩
    have seen : m ∈ x.original.diagnostics.marks := List.mem_of_getElem? pos
    have same : named = q := Option.some.inj
      ((any_mark_is_actual_original_diagnostic451 x.original.diagnostics seen).1.symm.trans child)
    have actualCycle : RootCycle p.state.base m.request := by simpa only [m,same] using cy
    obtain ⟨g,⟨found,_⟩,_⟩ :=
      (actual_cycle_has_exactly_one_internal_diagnostic452 x.original.diagnostics seen).mp actualCycle
    change g ∈ x.groups at found
    rw [empty] at found
    exact List.not_mem_nil found

private theorem some_rejected_plan_hits_actual_cyclic_child {s qs ts}
    (p : OrderedPlan s qs ts) (seen : Tree.rejected ∈ ts) :
    ∃ q ∈ qs, RootCycle s q := by
  induction p with
  | nil => simp at seen
  | @cons q qs t ts current tail ih =>
    rcases List.mem_cons.mp seen with eq | rest
    · cases current with
      | cycle h => exact ⟨q,List.mem_cons_self,h⟩
      | leaf _ => cases eq
    · obtain ⟨r,there,cy⟩ := ih rest
      exact ⟨r,List.mem_cons_of_mem _ there,cy⟩

/-- The grouped report of an old positive remains meaningful in the new
lane from the exact same original portion of its actual wire. This is
not the equality theorem for delegating all old Bool inputs, which is
separate and definitional. -/
theorem inherited_grouped_positive_replays_same_original_wire454
    {p : FullProblem} {r : GroupedReport} {w : ScopedLiteralInput}
    (passed : GroupedEntry453.check_full453 p (.grouped r) (.grouped w) = true) :
    check_full454 p (.rawGrouped r) (.rawGrouped w.original) = true := by
  cases read : readScopedLiteralReport p w with
  | none => simp [GroupedEntry453.check_full453,GroupedEntry453.checkGrouped453,read] at passed
  | some x =>
    have matched : matchesReport r (GroupedEntry453.exactReport x) = true := by
      have both : GroupedEntry453.wholeRosterCheck x = true ∧
          matchesReport r (GroupedEntry453.exactReport x) = true := by
        simpa [GroupedEntry453.check_full453,GroupedEntry453.checkGrouped453,read,
          Bool.and_eq_true] using passed
      exact both.2
    have cy := some_rejected_plan_hits_actual_cyclic_child x.localK2.plan x.localK2.containsRaw
    rw [x.sameOriginal] at cy
    have nonempty := (cyclic_group_nonempty_iff_has_actual_cyclic_child454 x.internal).mpr cy
    have fresh := read_both_retains_the_same_checked_profile_and_internal_groups452 read
    have sameReport : exactReport x.internal = GroupedEntry453.exactReport x := rfl
    simp [check_full454,check,fresh,nonempty,List.isEmpty_eq_false_iff,sameReport,matched]

theorem exact_grouped_raw_report_never_substitutes_parent_K2454
    {p : FullProblem} {r : GroupedReport} (valid : Exact p r) :
    ¬ RootCycle p.state.base p.root := by
  obtain ⟨x,_,_⟩ := valid
  exact x.original.parent.chosen.safe

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.SamePhase454
