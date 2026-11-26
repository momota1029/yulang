import Yulang.GeneralDeclarativeI65I74WhereEntry450

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem Result)
open RetainedFull445
open GeneralDeclarations (Clause)
open CommonRoleOutermostResolver (Tree)
open GeneralDeclarativeWitnessDeclaredState357 (point)

theorem Ordinal_from_actual_plan450 {s qs ts} (a : OrderedPlan s qs ts)
    {i : Nat} {q : I72.Request} (atReq : qs[i]? = some q) :
    ∃ t, ts[i]? = some t ∧ Nonempty (ChildPlan s q t) := by
  induction a generalizing i with
  | nil => simp at atReq
  | cons first _ ih =>
    cases i with
    | zero =>
      have eq := Option.some.inj atReq
      cases eq
      exact ⟨_,rfl,⟨first⟩⟩
    | succ i =>
      exact ih (by simpa using atReq)

theorem raw_rejection_iff_actual_child_cycle450 {s q t} (child : ChildPlan s q t) :
    t = .rejected ↔ RootCycle s q := by
  cases child with
  | cycle h => simp [h]
  | leaf l => simp [l.chosen.safe]

/-- Recover the exact report child and its geometric input occurrence
from any actual authored clause ordinal. A rejected child is precisely a
raw cycle for this original role/argument/occurrence, not merely a Bool. -/
theorem accepted_where_keeps_each_actual_child_position450 {p : FullProblem} {r : Result} {w : WhereWire}
    (ok : check_full450 p r (.whereRoot w) = true) :
    ∃ (a : OriginalRejection p.old), r = a.report ∧
      ∀ i c, a.parent.decl.requirements[i]? = some c →
        ∃ t, a.trees[i]? = some t ∧
          (t = .rejected ↔ RootCycle p.state.base
            ⟨p.root.occurrence ++ [i],literalDemand a.parent.chosen.roster.capture c⟩) := by
  obtain ⟨a,rpt,_,_⟩ := only_true_original_ordered_reports_are_accepted450 ok
  refine ⟨a,rpt,?_⟩
  intro i c written
  let req : I72.Request :=
    ⟨p.root.occurrence ++ [i],literalDemand a.parent.chosen.roster.capture c⟩
  have same : a.parent.children[i]? = some req := actual_child_at_original_clause450 a.parent written
  obtain ⟨t,atTree,⟨localPlan⟩⟩ := Ordinal_from_actual_plan450 a.plan same
  exact ⟨t,atTree,raw_rejection_iff_actual_child_cycle450 localPlan⟩

theorem each_read_leaf_has_actual_dictionary450 {s q t} (child : ChildPlan s q t)
    {key : Nat} (picked : t = .selected key []) (m : I72.Model) (fits : Fits s m) :
    I72.DictionaryEvidence s m q (.node key []) := by
  cases child with
  | cycle _ => cases picked
  | leaf a =>
    have keyEq : a.decl.id = key := Tree.selected.inj picked |>.1
    obtain ⟨_,_,_,_,dictionary⟩ := ListSites449.Frame.exact_framed_selection_assembly449 a
    rw [← keyEq]
    exact dictionary m fits

theorem each_accepted_successful_sibling_has_dictionary450 {p : FullProblem} {r : Result} {w : WhereWire}
    (ok : check_full450 p r (.whereRoot w) = true) :
    ∃ (a : OriginalRejection p.old), r = a.report ∧
      ∀ i c key, a.parent.decl.requirements[i]? = some c →
        a.trees[i]? = some (.selected key []) →
        ∀ m, FitsFull p.state m → I72.DictionaryEvidence p.state.base m
          ⟨p.root.occurrence ++ [i],literalDemand a.parent.chosen.roster.capture c⟩ (.node key []) := by
  obtain ⟨a,rpt,_,_⟩ := only_true_original_ordered_reports_are_accepted450 ok
  refine ⟨a,rpt,?_⟩
  intro i c key written selected m fit
  let req : I72.Request :=
    ⟨p.root.occurrence ++ [i],literalDemand a.parent.chosen.roster.capture c⟩
  have same : a.parent.children[i]? = some req := actual_child_at_original_clause450 a.parent written
  obtain ⟨t,atTree,⟨localPlan⟩⟩ := Ordinal_from_actual_plan450 a.plan same
  exact each_read_leaf_has_actual_dictionary450 localPlan (Option.some.inj (atTree.symm.trans selected)) m fit.1

end Yulang.GeneralDeclarativeI65.I72.WhereSites450
